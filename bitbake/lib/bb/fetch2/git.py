# ex:ts=4:sw=4:sts=4:et
# -*- tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*-
"""
BitBake 'Fetch' git implementation

git fetcher support the SRC_URI with format of:
SRC_URI = "git://some.host/somepath;OptionA=xxx;OptionB=xxx;..."

Supported SRC_URI options are:

- branch
   The git branch to retrieve from. The default is "master"

   This option also supports multiple branch fetching, with branches
   separated by commas.  In multiple branches case, the name option
   must have the same number of names to match the branches, which is
   used to specify the SRC_REV for the branch
   e.g:
   SRC_URI="git://some.host/somepath;branch=branchX,branchY;name=nameX,nameY"
   SRCREV_nameX = "xxxxxxxxxxxxxxxxxxxx"
   SRCREV_nameY = "YYYYYYYYYYYYYYYYYYYY"

- tag
    The git tag to retrieve. The default is "master"

- protocol
   The method to use to access the repository. Common options are "git",
   "http", "https", "file", "ssh" and "rsync". The default is "git".

- rebaseable
   rebaseable indicates that the upstream git repo may rebase in the future,
   and current revision may disappear from upstream repo. This option will
   remind fetcher to preserve local cache carefully for future use.
   The default value is "0", set rebaseable=1 for rebaseable git repo.

- nocheckout
   Don't checkout source code when unpacking. set this option for the recipe
   who has its own routine to checkout code.
   The default is "0", set nocheckout=1 if needed.

- bareclone
   Create a bare clone of the source code and don't checkout the source code
   when unpacking. Set this option for the recipe who has its own routine to
   checkout code and tracking branch requirements.
   The default is "0", set bareclone=1 if needed.

- nobranch
   Don't check the SHA validation for branch. set this option for the recipe
   referring to commit which is valid in tag instead of branch.
   The default is "0", set nobranch=1 if needed.

"""

#Copyright (C) 2005 Richard Purdie
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

import collections
import errno
import itertools
import os
import re
import subprocess
import tempfile
import bb
import errno
from   bb    import data
from   bb.fetch2 import FetchMethod
from   bb.fetch2 import runfetchcmd
from   bb.fetch2 import logger


def iter_except(func, exception, start=None):
    """Yield a function repeatedly until it raises an exception."""
    try:
        if start is not None:
            yield start()
        while True:
            yield func()
    except exception:
        pass


def iter_extend(iterable, length, obj=None):
    """Ensure that iterable is the specified length by extending with obj"""
    return itertools.islice(itertools.chain(iterable, itertools.repeat(obj)), length)


class Git(FetchMethod):
    """Class to fetch a module or modules from git repositories"""
    def init(self, d):
        pass

    def supports(self, ud, d):
        """
        Check to see if a given url can be fetched with git.
        """
        return ud.type in ['git']

    def supports_checksum(self, urldata):
        return False

    def urldata_init(self, ud, d):
        """
        init git specific variable within url data
        so that the git method like latest_revision() can work
        """
        if 'protocol' in ud.parm:
            ud.proto = ud.parm['protocol']
        elif not ud.host:
            ud.proto = 'file'
        else:
            ud.proto = "git"

        if not ud.proto in ('git', 'file', 'ssh', 'http', 'https', 'rsync'):
            raise bb.fetch2.ParameterError("Invalid protocol type", ud.url)

        ud.nocheckout = ud.parm.get("nocheckout","0") == "1"

        ud.rebaseable = ud.parm.get("rebaseable","0") == "1"

        ud.nobranch = ud.parm.get("nobranch","0") == "1"

        # bareclone implies nocheckout
        ud.bareclone = ud.parm.get("bareclone","0") == "1"
        if ud.bareclone:
            ud.nocheckout = 1
  
        ud.unresolvedrev = {}
        branches = ud.parm.get("branch", "master").split(',')
        if len(branches) != len(ud.names):
            raise bb.fetch2.ParameterError("The number of name and branch parameters is not balanced", ud.url)

        ud.shallow = d.getVar("BB_GIT_SHALLOW", True) == "1"
        ud.shallow_revs = (d.getVar("BB_GIT_SHALLOW_REVS", True) or "").split()
        trim_refs = d.getVar("BB_GIT_SHALLOW_TRIM_REFS", True)
        ud.trim_refs = not trim_refs or trim_refs == "0"
        ud.shallow_extra_refs = (d.getVar("BB_GIT_SHALLOW_EXTRA_REFS", True) or "").split()

        depth_default = d.getVar("BB_GIT_SHALLOW_DEPTH", True)
        if depth_default is not None:
            try:
                depth_default = int(depth_default)
            except ValueError:
                raise bb.fetch2.FetchError("Invalid depth for BB_GIT_SHALLOW_DEPTH: %s" % depth_default)
        else:
            depth_default = 1
        ud.shallow_depths = collections.defaultdict(lambda: depth_default)

        ud.branches = {}
        for pos, name in enumerate(ud.names):
            branch = branches[pos]
            ud.branches[name] = branch
            ud.unresolvedrev[name] = branch

            shallow_depth = d.getVar("BB_GIT_SHALLOW_DEPTH_%s" % name, True)
            if shallow_depth and shallow_depth != "0":
                try:
                    shallow_depth = int(shallow_depth)
                except ValueError:
                    raise bb.fetch2.FetchError("Invalid depth for BB_GIT_SHALLOW_DEPTH_%s: %s" % (name, shallow_depth))
                else:
                    ud.shallow_depths[name] = shallow_depth

        ud.basecmd = data.getVar("FETCHCMD_git", d, True) or "git -c core.fsyncobjectfiles=0"

        write_tarballs = d.getVar("BB_GENERATE_MIRROR_TARBALLS", True) or "0"
        ud.write_tarballs = write_tarballs != "0" or ud.rebaseable
        ud.write_shallow_tarballs = (d.getVar("BB_GENERATE_SHALLOW_TARBALLS", True) or write_tarballs) != "0"

        ud.setup_revisons(d)

        for name in ud.names:
            # Ensure anything that doesn't look like a sha256 checksum/revision is translated into one
            if not ud.revisions[name] or len(ud.revisions[name]) != 40  or (False in [c in "abcdef0123456789" for c in ud.revisions[name]]):
                if ud.revisions[name]:
                    ud.unresolvedrev[name] = ud.revisions[name]
                ud.revisions[name] = self.latest_revision(ud, d, name)

        gitsrcname = '%s%s' % (ud.host.replace(':', '.'), ud.path.replace('/', '.').replace('*', '.'))
        if gitsrcname.startswith('.'):
            gitsrcname = gitsrcname[1:]

        # for rebaseable git repo, it is necessary to keep mirror tar ball
        # per revision, so that even the revision disappears from the
        # upstream repo in the future, the mirror will remain intact and still
        # contains the revision
        if ud.rebaseable:
            for name in ud.names:
                gitsrcname = gitsrcname + '_' + ud.revisions[name]

        dl_dir = d.getVar("DL_DIR", True)
        gitdir = d.getVar("GITDIR", True) or (dl_dir + "/git2/")
        ud.clonedir = os.path.join(gitdir, gitsrcname)
        ud.localfile = ud.clonedir

        ud.mirrortarball = 'git2_%s.tar.gz' % gitsrcname
        ud.fullmirror = os.path.join(dl_dir, ud.mirrortarball)
        if ud.shallow:
            tarballname = gitsrcname
            if ud.shallow_revs:
                tarballname = "%s_%s" % (tarballname, "_".join(sorted(ud.shallow_revs)))

            for name, revision in sorted(ud.revisions.iteritems()):
                tarballname = "%s_%s" % (tarballname, ud.revisions[name][:7])
                depth = ud.shallow_depths[name]
                if depth:
                    tarballname = "%s-%s" % (tarballname, depth)

            if ud.trim_refs:
                if not ud.nobranch:
                    shallow_refs = ud.branches.itervalues()
                    shallow_refs = itertools.chain(shallow_refs, ud.shallow_extra_refs)
                    tarballname = "%s_%s" % (tarballname, "_".join(sorted(shallow_refs)).replace('/', '.'))
                ud.shallowtarball = 'gitshallow_%s.tar.gz' % tarballname
            else:
                ud.shallowtarball = 'gitshallowall_%s.tar.gz' % tarballname
            ud.fullshallow = os.path.join(dl_dir, ud.shallowtarball)
            ud.mirrortarballs = [ud.shallowtarball, ud.mirrortarball]

    def localpath(self, ud, d):
        return ud.clonedir

    def need_update(self, ud, d):
        if not os.path.exists(ud.clonedir):
            return True
        os.chdir(ud.clonedir)
        for name in ud.names:
            if not self._contains_ref(ud, d, name):
                return True
        if ud.shallow and ud.write_shallow_tarballs and not os.path.exists(ud.fullshallow):
            return True
        if ud.write_tarballs and not os.path.exists(ud.fullmirror):
            return True
        return False

    def try_premirror(self, ud, d):
        # If we don't do this, updating an existing checkout with only premirrors
        # is not possible
        if d.getVar("BB_FETCH_PREMIRRORONLY", True) is not None:
            return True
        if os.path.exists(ud.clonedir):
            return False
        return True

    def download(self, ud, d):
        """Fetch url"""

        no_clone = not os.path.exists(ud.clonedir)
        need_update = no_clone or self.need_update(ud, d)

        # A current clone is preferred to either tarball, a shallow tarball is
        # preferred to an out of date clone, and a missing clone will use
        # either tarball.
        if ud.shallow and os.path.exists(ud.fullshallow) and need_update:
            ud.localpath = ud.fullshallow
            return
        elif os.path.exists(ud.fullmirror) and no_clone:
            bb.utils.mkdirhier(ud.clonedir)
            os.chdir(ud.clonedir)
            runfetchcmd("tar -xzf %s" % (ud.fullmirror), d)

        repourl = self._get_repo_url(ud)

        # If the repo still doesn't exist, fallback to cloning it
        if not os.path.exists(ud.clonedir):
            # We do this since git will use a "-l" option automatically for local urls where possible
            if repourl.startswith("file://"):
                repourl = repourl[7:]
            clone_cmd = "%s clone --bare --mirror %s %s" % (ud.basecmd, repourl, ud.clonedir)
            if ud.proto.lower() != 'file':
                bb.fetch2.check_network_access(d, clone_cmd)
            runfetchcmd(clone_cmd, d)

        os.chdir(ud.clonedir)
        # Update the checkout if needed
        needupdate = False
        for name in ud.names:
            if not self._contains_ref(ud, d, name):
                needupdate = True
        if needupdate:
            try: 
                runfetchcmd("%s remote rm origin" % ud.basecmd, d) 
            except bb.fetch2.FetchError:
                logger.debug(1, "No Origin")

            runfetchcmd("%s remote add --mirror=fetch origin %s" % (ud.basecmd, repourl), d)
            fetch_cmd = "%s fetch -f --prune %s refs/*:refs/*" % (ud.basecmd, repourl)
            if ud.proto.lower() != 'file':
                bb.fetch2.check_network_access(d, fetch_cmd, ud.url)
            runfetchcmd(fetch_cmd, d)
            runfetchcmd("%s prune-packed" % ud.basecmd, d)
            runfetchcmd("%s pack-redundant --all | xargs -r rm" % ud.basecmd, d)
            try:
                os.unlink(ud.fullmirror)
            except OSError as exc:
                if exc.errno != errno.ENOENT:
                    raise
        os.chdir(ud.clonedir)
        for name in ud.names:
            if not self._contains_ref(ud, d, name):
                raise bb.fetch2.FetchError("Unable to find revision %s in branch %s even from upstream" % (ud.revisions[name], ud.branches[name]))

    def build_mirror_data(self, ud, d):
        if ud.shallow and ud.write_shallow_tarballs:
            if not os.path.exists(ud.fullshallow):
                if os.path.islink(ud.fullshallow):
                    os.unlink(ud.fullshallow)
                tempdir = tempfile.mkdtemp(dir=d.getVar('DL_DIR', True))
                shallowclone = os.path.join(tempdir, 'git')
                try:
                    repourl = self._get_repo_url(ud)
                    branchinfo = dict((name, (ud.shallow_depths[name], ud.revisions[name], ud.branches[name])) for name in ud.names)
                    self._populate_shallowclone(repourl, ud.clonedir, shallowclone, ud.basecmd, branchinfo, ud.nobranch, ud.trim_refs, ud.shallow_extra_refs, ud.shallow_revs, ud.bareclone, d)

                    logger.info("Creating tarball of git repository")
                    runfetchcmd("tar -czf %s %s" % (ud.fullshallow, os.path.join(".")), d)
                    runfetchcmd("touch %s.done" % ud.fullshallow, d)
                finally:
                    bb.utils.remove(tempdir, recurse=True)
        elif ud.write_tarballs and not os.path.exists(ud.fullmirror):
            if os.path.islink(ud.fullmirror):
                os.unlink(ud.fullmirror)
            os.chdir(ud.clonedir)
            logger.info("Creating tarball of git repository")
            runfetchcmd("tar -czf %s %s" % (ud.fullmirror, os.path.join(".")), d)
            runfetchcmd("touch %s.done" % ud.fullmirror, d)

    def _populate_shallowclone(self, repourl, source, dest, gitcmd, branchinfo, nobranch, trim_refs, extra_refs, shallow_revisions, bareclone, d):
        if shallow_revisions is None:
            shallow_revisions = []

        # Map depths to revisions
        to_parse = []
        for depth, revision, branch in branchinfo.itervalues():
            if not depth:
                continue

            to_parse.append('%s~%d^{}' % (revision, depth - 1))

        parsed = runfetchcmd("GIT_DIR='%s' %s rev-parse %s" % (source, gitcmd, " ".join(to_parse)), d)
        shallow_revisions.extend(parsed.splitlines())

        cloneflags = "-s -n"
        if bareclone:
            cloneflags += " --mirror"
        runfetchcmd("%s clone %s %s %s" % (gitcmd, cloneflags, source, dest), d)

        os.chdir(dest)

        shallow_branches = []
        shallow_branches.extend(extra_refs)
        for name, (depth, revision, branch) in branchinfo.iteritems():
            if nobranch:
                ref = "refs/shallow/%s" % name
            else:
                ref = "refs/remotes/origin/%s" % branch

            if trim_refs:
                shallow_branches.append(ref)
            runfetchcmd("%s update-ref %s %s" % (gitcmd, ref, revision), d)

        if trim_refs:
            self.filter_refs(gitcmd, d, shallow_branches)

        git_dir = runfetchcmd('%s rev-parse --git-dir' % gitcmd, d).rstrip()
        self._make_repo_shallow(shallow_revisions, git_dir, gitcmd, d, branches=shallow_branches or None)

        alternates_file = os.path.join(git_dir, "objects", "info", "alternates")
        os.unlink(alternates_file)

    def _make_repo_shallow(self, revisions, git_dir, gitcmd, d, branches=None):
        if branches is not None:
            refs = branches
        else:
            refs = self.get_all_refs(gitcmd, d, lambda r, t: not t or t == 'commit')

        parsed_revs = runfetchcmd('%s rev-parse %s' % (gitcmd, ' '.join('%s^{}' % i for i in revisions)), d)
        queue = collections.deque(r.rstrip() for r in parsed_revs.splitlines())
        seen = set()

        shallow_file = os.path.join(git_dir, 'shallow')
        try:
            os.unlink(shallow_file)
        except OSError as exc:
            if exc.errno != errno.ENOENT:
                raise

        for rev in iter_except(queue.popleft, IndexError):
            if rev in seen:
                continue

            bb.note("Processing shallow revision: %s" % rev)
            parent_output = runfetchcmd('%s rev-parse %s^@' % (gitcmd, rev), d)
            parents = [p.rstrip() for p in parent_output.splitlines()]
            with open(shallow_file, 'a') as f:
                f.write(rev + '\n')
            seen.add(rev)

            for parent in parents:
                for ref in refs:
                    try:
                        merge_base = runfetchcmd('%s merge-base %s %s' % (gitcmd, parent, ref), d).rstrip()
                    except bb.fetch2.FetchError:
                        continue
                    queue.append(merge_base)

        runfetchcmd('%s reflog expire --expire-unreachable=now --all' % gitcmd, d)
        runfetchcmd('%s repack -ad' % gitcmd, d)
        runfetchcmd('%s prune --expire now' % gitcmd, d)

    @classmethod
    def get_all_refs(cls, gitcmd, d, ref_filter=None):
        """Return all the existing refs in this repository, optionally filtering the refs."""
        ref_output = runfetchcmd('{} for-each-ref "--format=%(refname)" "%(*objecttype)"'.format(gitcmd), d)
        ref_split = (tuple(iter_extend(l.rstrip().rsplit('\t', 1), 2)) for l in ref_output.splitlines())
        if ref_filter:
            ref_split = (e for e in ref_split if ref_filter(*e))
        refs = [r for r, _ in ref_split]
        return refs

    @classmethod
    def filter_refs(cls, gitcmd, d, refs):
        """Remove all but the specified refs from the git repository."""
        all_refs = cls.get_all_refs(gitcmd, d)
        full_refs = runfetchcmd('%s rev-parse --symbolic-full-name %s' % (gitcmd, ' '.join(refs)), d).splitlines()
        to_remove = set(all_refs) - set(full_refs)
        if to_remove:
            p = bb.process.Popen(['xargs', '-0', '-n', '1', 'git', 'update-ref', '-d', '--no-deref'], stderr=subprocess.PIPE)
            p.communicate(''.join(l + '\0' for l in to_remove))

    def unpack(self, ud, destdir, d):
        """ unpack the downloaded src to destdir"""

        subdir = ud.parm.get("subpath", "")
        if subdir != "":
            readpathspec = ":%s" % subdir
            def_destsuffix = "%s/" % os.path.basename(subdir.rstrip('/'))
        else:
            readpathspec = ""
            def_destsuffix = "git/"

        destsuffix = ud.parm.get("destsuffix", def_destsuffix)
        destdir = ud.destdir = os.path.join(destdir, destsuffix)
        if os.path.exists(destdir):
            bb.utils.prunedir(destdir)

        if ud.shallow and (not os.path.exists(ud.clonedir) or self.need_update(ud, d)):
            bb.utils.mkdirhier(destdir)
            os.chdir(destdir)
            runfetchcmd("tar -xzf %s" % ud.fullshallow, d)
        else:
            cloneflags = "-s -n"
            if ud.bareclone:
                cloneflags += " --mirror"

            runfetchcmd("%s clone %s %s/ %s" % (ud.basecmd, cloneflags, ud.clonedir, destdir), d)

        os.chdir(destdir)
        repourl = self._get_repo_url(ud)
        runfetchcmd("%s remote set-url origin %s" % (ud.basecmd, repourl), d)
        if not ud.nocheckout:
            if subdir != "":
                runfetchcmd("%s read-tree %s%s" % (ud.basecmd, ud.revisions[ud.names[0]], readpathspec), d)
                runfetchcmd("%s checkout-index -q -f -a" % ud.basecmd, d)
            elif not ud.nobranch:
                branchname =  ud.branches[ud.names[0]]
                runfetchcmd("%s checkout -B %s %s" % (ud.basecmd, branchname, \
                            ud.revisions[ud.names[0]]), d)
                runfetchcmd("%s branch --set-upstream %s origin/%s" % (ud.basecmd, branchname, \
                            branchname), d)
            else:
                runfetchcmd("%s checkout %s" % (ud.basecmd, ud.revisions[ud.names[0]]), d)

        return True

    def clean(self, ud, d):
        """ clean the git directory """

        bb.utils.remove(ud.localpath, True)
        bb.utils.remove(ud.fullmirror)
        bb.utils.remove(ud.fullmirror + ".done")

    def supports_srcrev(self):
        return True

    def _contains_ref(self, ud, d, name):
        cmd = ""
        if ud.nobranch:
            cmd = "%s log --pretty=oneline -n 1 %s -- 2> /dev/null | wc -l" % (
                ud.basecmd, ud.revisions[name])
        else:
            cmd =  "%s branch --contains %s --list %s 2> /dev/null | wc -l" % (
                ud.basecmd, ud.revisions[name], ud.branches[name])
        try:
            output = runfetchcmd(cmd, d, quiet=True)
        except bb.fetch2.FetchError:
            return False
        if len(output.split()) > 1:
            raise bb.fetch2.FetchError("The command '%s' gave output with more then 1 line unexpectedly, output: '%s'" % (cmd, output))
        return output.split()[0] != "0"

    def _get_repo_url(self, ud):
        """
        Return the repository URL
        """
        if ud.user:
            username = ud.user + '@'
        else:
            username = ""
        return "%s://%s%s%s" % (ud.proto, username, ud.host, ud.path)

    def _revision_key(self, ud, d, name):
        """
        Return a unique key for the url
        """
        return "git:" + ud.host + ud.path.replace('/', '.') + ud.unresolvedrev[name]

    def _lsremote(self, ud, d, search):
        """
        Run git ls-remote with the specified search string
        """
        repourl = self._get_repo_url(ud)
        cmd = "%s ls-remote %s %s" % \
              (ud.basecmd, repourl, search)
        if ud.proto.lower() != 'file':
            bb.fetch2.check_network_access(d, cmd)
        output = runfetchcmd(cmd, d, True)
        if not output:
            raise bb.fetch2.FetchError("The command %s gave empty output unexpectedly" % cmd, ud.url)
        return output

    def _latest_revision(self, ud, d, name):
        """
        Compute the HEAD revision for the url
        """
        output = self._lsremote(ud, d, "")
        # Tags of the form ^{} may not work, need to fallback to other form
        if ud.unresolvedrev[name][:5] == "refs/":
            head = ud.unresolvedrev[name]
            tag = ud.unresolvedrev[name]
        else:
            head = "refs/heads/%s" % ud.unresolvedrev[name]
            tag = "refs/tags/%s" % ud.unresolvedrev[name]
        for s in [head, tag + "^{}", tag]:
            for l in output.strip().split('\n'):
                sha1, ref = l.split()
                if s == ref:
                    return sha1
        raise bb.fetch2.FetchError("Unable to resolve '%s' in upstream git repository in git ls-remote output for %s" % \
            (ud.unresolvedrev[name], ud.host+ud.path))

    def latest_versionstring(self, ud, d):
        """
        Compute the latest release name like "x.y.x" in "x.y.x+gitHASH"
        by searching through the tags output of ls-remote, comparing
        versions and returning the highest match.
        """
        pupver = ('', '')

        tagregex = re.compile(d.getVar('UPSTREAM_CHECK_GITTAGREGEX', True) or "(?P<pver>([0-9][\.|_]?)+)")
        try:
            output = self._lsremote(ud, d, "refs/tags/*")
        except bb.fetch2.FetchError or bb.fetch2.NetworkAccess:
            return pupver

        verstring = ""
        revision = ""
        for line in output.split("\n"):
            if not line:
                break

            tag_head = line.split("/")[-1]
            # Ignore non-released branches
            m = re.search("(alpha|beta|rc|final)+", tag_head)
            if m:
                continue

            # search for version in the line
            tag = tagregex.search(tag_head)
            if tag == None:
                continue

            tag = tag.group('pver')
            tag = tag.replace("_", ".")

            if verstring and bb.utils.vercmp(("0", tag, ""), ("0", verstring, "")) < 0:
                continue

            verstring = tag
            revision = line.split()[0]
            pupver = (verstring, revision)

        return pupver

    def _build_revision(self, ud, d, name):
        return ud.revisions[name]

    def gitpkgv_revision(self, ud, d, name):
        """
        Return a sortable revision number by counting commits in the history
        Based on gitpkgv.bblass in meta-openembedded
        """
        rev = self._build_revision(ud, d, name)
        localpath = ud.localpath
        rev_file = os.path.join(localpath, "oe-gitpkgv_" + rev)
        if not os.path.exists(localpath):
            commits = None
        else:
            if not os.path.exists(rev_file) or not os.path.getsize(rev_file):
                from pipes import quote
                commits = bb.fetch2.runfetchcmd(
                        "git rev-list %s -- | wc -l" % (quote(rev)),
                        d, quiet=True).strip().lstrip('0')
                if commits:
                    open(rev_file, "w").write("%d\n" % int(commits))
            else:
                commits = open(rev_file, "r").readline(128).strip()
        if commits:
            return False, "%s+%s" % (commits, rev[:7])
        else:
            return True, str(rev)

    def checkstatus(self, fetch, ud, d):
        try:
            self._lsremote(ud, d, "")
            return True
        except FetchError:
            return False
