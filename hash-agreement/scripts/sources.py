#!/usr/bin/env python3
"""Fetch the two upstream libraries at their pins and write the files the generators read.

usage: sources.py     write build/sources/ from the pins in inputs/SOURCES.txt

- Noir: noir-lang/poseidon at the pinned tag. A shallow clone of the tag (as nargo makes it) is
  kept in DEPS_CACHE/<commit>. A fresh clone must resolve the tag to the pinned commit, so a moved
  tag fails; a run that finds the commit in the cache does not ask upstream again. The four files
  are read as git blobs at that commit, never from a checkout.
- Solidity: the soldeer archive of poseidon-solidity 0.0.5, the URL and checksum that the pool's
  soldeer.lock pins at pocs a04b8b3. The zip is kept in DEPS_CACHE/soldeer/<checksum>.zip after
  its sha256 matches the checksum; one member is read from it.
Each written file must then match its sha256 in scripts/common.py.

DEPS_CACHE (default: hash-agreement/.deps) has the same layout as verifier-reproduction's, so one
directory set for both packages holds one clone of noir-lang/poseidon. The network is needed
only when the cache lacks the commit or the zip.
"""
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile

import common as c

OUT = os.path.join(c.PKG, 'build', 'sources')


class Fail(Exception):
    pass


def pins():
    out = {}
    for line in open(os.path.join(c.INPUTS, 'SOURCES.txt')):
        if line.strip():
            k, v = line.rstrip('\n').split(' ', 1)
            out[k] = v
    return out


def git(*args, cwd=None):
    return subprocess.run(['git', *args], cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def noir_repo(p, cache):
    commit, tag, url = p['noir_commit'], p['noir_tag'], p['noir_url']
    repo = os.path.join(cache, commit)
    if git('-C', repo, 'cat-file', '-e', commit + '^{commit}').returncode == 0:
        return repo, 'cache'
    os.makedirs(cache, exist_ok=True)
    tmp = tempfile.mkdtemp(prefix='clone.', dir=cache)
    try:
        r = git('-c', 'advice.detachedHead=false', 'clone', '-q', '--depth', '1', '--branch', tag, url,
                os.path.join(tmp, 'r'))
        if r.returncode != 0:
            raise Fail(f'cannot clone {url} at tag {tag}: {r.stderr.decode(errors="replace").strip()}')
        got = git('-C', os.path.join(tmp, 'r'), 'rev-parse', 'HEAD').stdout.decode().strip()
        if got != commit:
            raise Fail(f'{url} tag {tag} is at {got}, pinned {commit}')
        shutil.rmtree(repo, ignore_errors=True)
        os.rename(os.path.join(tmp, 'r'), repo)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return repo, 'clone'


def soldeer_zip(p, cache):
    want = p['soldeer_checksum']
    path = os.path.join(cache, 'soldeer', want + '.zip')
    if os.path.exists(path) and c.sha256_file(path) == want:
        return path, 'cache'
    try:
        data = urllib.request.urlopen(p['soldeer_url'], timeout=60).read()
    except Exception as e:
        raise Fail(f'cannot download {p["soldeer_url"]}: {e}')
    got = hashlib.sha256(data).hexdigest()
    if got != want:
        raise Fail(f'soldeer zip sha256 {got}, pinned checksum {want}')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path + '.tmp', 'wb') as f:
        f.write(data)
    os.replace(path + '.tmp', path)
    return path, 'download'


def write(rel, data, want):
    got = hashlib.sha256(data).hexdigest()
    if got != want:
        raise Fail(f'{rel}: sha256 {got}, pinned {want} (scripts/common.py)')
    dst = os.path.join(OUT, rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    with open(dst, 'wb') as f:
        f.write(data)


def main():
    p = pins()
    cache = os.path.abspath(os.environ.get('DEPS_CACHE') or os.path.join(c.PKG, '.deps'))
    shutil.rmtree(OUT, ignore_errors=True)
    repo, how = noir_repo(p, cache)
    for rel, want in c.NOIR_SHA.items():
        r = git('-C', repo, 'cat-file', 'blob', f'{p["noir_commit"]}:{p["noir_dir"]}/{rel}')
        if r.returncode != 0:
            raise Fail(f'{p["noir_dir"]}/{rel} is not in {p["noir_url"]} at {p["noir_commit"]}')
        write(os.path.join('noir', rel), r.stdout, want)
    print(f'sources: {p["noir_url"]} {p["noir_tag"]} at {p["noir_commit"]} ({how}), '
          f'{len(c.NOIR_SHA)} files match their sha256')
    path, how = soldeer_zip(p, cache)
    try:
        data = zipfile.ZipFile(path).read(p['soldeer_member'])
    except KeyError:
        raise Fail(f'{p["soldeer_member"]} is not in the soldeer zip')
    write('PoseidonT3.sol', data, c.SOL_SHA)
    print(f'sources: soldeer zip {p["soldeer_checksum"]} ({how}), {p["soldeer_member"]} matches its sha256')


if __name__ == '__main__':
    if sys.argv[1:]:
        print(__doc__)
        sys.exit(2)
    try:
        main()
    except Fail as e:
        print(f'FAIL sources: {e}')
        sys.exit(1)
