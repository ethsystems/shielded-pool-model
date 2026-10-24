#!/usr/bin/env python3
"""Check the pins of PINS.sha256.

  pins.py [--fetched] [--lakefile F] [--manifest F] [--packages DIR] [--model-root DIR]

Checks, in order:

- lean-toolchain names the pinned Lean;
- lakefile.toml (parsed with tomllib) has exactly two requires, VCV-io and Mathlib, each with
  only a name, a git URL and a rev, at the pinned URL and revision;
- lake-manifest.json: packagesDir is .lake/packages; every package is of type git, with no
  subDir and a full commit as rev; the direct packages are the two requires, at the same URL
  and revision; the file has its pinned SHA-256, so the inherited packages are pinned too;
- each checkout of the manifest under DIR (default .lake/packages) is its own git repository,
  at the manifest rev, with the manifest URL as origin; it has no tracked change, no file
  hidden by assume-unchanged or skip-worktree, no untracked file, and no ignored file outside
  its .lake/ directory; VCV-io's own manifest pins the same Mathlib. Without --fetched a
  missing checkout is skipped; with --fetched (after lake exe cache get) it is a failure;
- the three model files (paths relative to the package, read under --model-root, default the
  package) have their pinned SHA-256.

The options let scripts/controls.py point the checks at altered copies.
Prints the first failure as "PINS FAIL: ..." and exits 1.
"""
import hashlib
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent


def fail(msg):
    print(f'PINS FAIL: {msg}')
    sys.exit(1)


def git(d, *args):
    return subprocess.run(['git', '-C', str(d), *args], capture_output=True, text=True).stdout.strip()


def sha256(f):
    return hashlib.sha256(f.read_bytes()).hexdigest() if f.is_file() else 'missing'


def check_checkout(name, p, d):
    if Path(git(d, 'rev-parse', '--show-toplevel') or '/').resolve() != d.resolve():
        fail(f'{d} is not a git checkout of its own')
    head = git(d, 'rev-parse', 'HEAD')
    if head != p['rev']:
        fail(f'{d} is at {head!r}, not {p["rev"]}')
    origin = git(d, 'remote', 'get-url', 'origin')
    if origin != p['url']:
        fail(f'{d} has origin {origin!r}, not {p["url"]}')
    hidden = [l for l in git(d, 'ls-files', '-v').splitlines() if l[:1].islower() or l[:1] == 'S']
    if hidden:
        fail(f'the {name} checkout hides a tracked file from git status: {hidden[0]}')
    dirty = git(d, 'status', '--porcelain', '--untracked-files=all')
    if dirty:
        fail(f'the {name} checkout has changes: {dirty.splitlines()[0]}')
    ignored = [l for l in git(d, 'ls-files', '--others', '--ignored', '--exclude-standard',
                              '--directory').splitlines() if not l.startswith('.lake/')]
    if ignored:
        fail(f'the {name} checkout has an ignored file outside .lake/: {ignored[0]}')


def main():
    a = sys.argv[1:]
    opt = lambda k, d: Path(a[a.index(k) + 1]) if k in a else d
    fetched = '--fetched' in a
    lakefile = opt('--lakefile', PKG / 'lakefile.toml')
    manifest = opt('--manifest', PKG / 'lake-manifest.json')
    packages = opt('--packages', PKG / '.lake' / 'packages')
    model_root = opt('--model-root', PKG)
    text = (PKG / 'PINS.sha256').read_text()
    pin = dict(re.findall(r'^# (\w+) (\S+)$', text, re.M))
    hashes = {path: sha for sha, path in re.findall(r'^([0-9a-f]{64})  (\S+)$', text, re.M)}
    if (PKG / 'lean-toolchain').read_text().strip() != f"leanprover/lean4:{pin['lean']}":
        fail(f"lean-toolchain is not leanprover/lean4:{pin['lean']}")

    want = {'VCVio': (pin['vcvio_url'], pin['vcvio_rev']), 'mathlib': (pin['mathlib_url'], pin['mathlib_rev'])}
    requires = tomllib.loads(lakefile.read_text()).get('require', [])
    names = [r.get('name') for r in requires]
    if sorted(names) != sorted(want):
        fail(f'lakefile.toml requires {names}, not exactly {sorted(want)}')
    for r in requires:
        name = r['name']
        if set(r) != {'name', 'git', 'rev'} or (r['git'], r['rev']) != want[name]:
            fail(f'lakefile.toml does not require {name} at {want[name][0]} {want[name][1]} '
                 f'(and nothing else): {r}')

    mj = json.loads(manifest.read_text())
    if mj.get('packagesDir') != '.lake/packages':
        fail(f"lake-manifest.json has packagesDir {mj.get('packagesDir')!r}, not '.lake/packages'")
    m = {}
    for p in mj['packages']:
        if p.get('name') in m:
            fail(f"lake-manifest.json lists {p.get('name')} twice")
        m[p.get('name')] = p
    for name in want:
        p = m.get(name, {})
        if (p.get('url'), p.get('rev')) != want[name]:
            fail(f"lake-manifest.json resolves {name} to {p.get('url')} {p.get('rev')}, "
                 f"not {want[name][0]} {want[name][1]}")
    for name, p in m.items():
        if (p.get('type') != 'git' or p.get('subDir') is not None
                or not re.fullmatch(r'[0-9a-f]{40}', p.get('rev') or '') or not p.get('url')):
            fail(f'lake-manifest.json entry {name} is not a git package at a full commit with no subDir')
        if p.get('inherited') is not True and name not in want:
            fail(f'lake-manifest.json has a direct package {name} that lakefile.toml does not require')
    got = sha256(manifest)
    if got != hashes['lake-manifest.json']:
        fail(f"lake-manifest.json has sha256 {got}, not the pinned {hashes['lake-manifest.json']}")
    print(f"pins: lakefile.toml requires only VCV-io {pin['vcvio_rev'][:8]} and Mathlib "
          f"{pin['mathlib_rev'][:8]}; lake-manifest.json ({len(m)} git packages) matches them and its pin")

    checked = []
    for name, p in m.items():
        d = packages / name
        if not d.is_dir():
            if fetched:
                fail(f'{d} is missing after the fetch')
            continue
        check_checkout(name, p, d)
        checked.append(name)
    if 'VCVio' in checked:
        vm = {p['name']: p['rev'] for p in json.loads((packages / 'VCVio' / 'lake-manifest.json').read_text())['packages']}
        if vm.get('mathlib') != pin['mathlib_rev']:
            fail(f"VCV-io's lake-manifest.json pins Mathlib {vm.get('mathlib')}, not {pin['mathlib_rev']}")
    if checked:
        print(f'pins: {len(checked)} of {len(m)} checkouts are at their manifest revision and URL, with no '
              'tracked change, no untracked file and no ignored file outside .lake/')
    else:
        print('pins: no fetched packages yet; checkouts not checked')

    for path, sha in hashes.items():
        if path == 'lake-manifest.json':
            continue
        got = sha256(model_root / path)
        if got != sha:
            fail(f'model file {path} has sha256 {got}, not the pinned {sha}')
    print('pins: the three model files (State.lean, Tx.lean, Events.lean) match PINS.sha256')


if __name__ == '__main__':
    main()
