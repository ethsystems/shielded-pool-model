#!/usr/bin/env python3
"""Check extracted soldeer packages against the `integrity` values of a soldeer.lock.

Usage: soldeer-integrity.py <soldeer.lock> <dependencies-dir>
The hash follows soldeer-core's hash_folder: one sha256 per walked entry (the root dir
and every subdir by relative path; every file by relative path then the sha256 of its
content), `.git` skipped, the entry hashes sorted and hashed again. This reimplementation
reproduces the three integrity values of the soldeer.lock at ethsystems/pocs a04b8b3.
Git dependencies have no integrity value; the caller checks them by tree id.
"""
import hashlib, os, re, sys


def integrity(root):
    hs = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d != ".git"]
        rel = os.path.relpath(dp, root)
        hs.append(hashlib.sha256(("" if rel == "." else rel).encode()).digest())
        for f in fn:
            h = hashlib.sha256(os.path.relpath(os.path.join(dp, f), root).encode())
            h.update(hashlib.sha256(open(os.path.join(dp, f), "rb").read()).digest())
            hs.append(h.digest())
    h = hashlib.sha256()
    for x in sorted(hs):
        h.update(x)
    return h.hexdigest()


lock, deps = sys.argv[1:3]
bad = 0
for blk in open(lock).read().split("[[dependencies]]")[1:]:
    name = re.search(r'name = "([^"]+)"', blk).group(1)
    ver = re.search(r'version = "([^"]+)"', blk).group(1)
    m = re.search(r'integrity = "([0-9a-f]{64})"', blk)
    if not m:
        print(f"{name}-{ver}: git dependency, rev {re.search(r'rev = \"([0-9a-f]+)\"', blk).group(1)}")
        continue
    got = integrity(os.path.join(deps, f"{name}-{ver}"))
    ok = got == m.group(1)
    bad += not ok
    print(f"{name}-{ver}: integrity {got} lock {m.group(1)} {'OK' if ok else 'MISMATCH'}")
sys.exit(1 if bad else 0)
