#!/usr/bin/env python3
"""Check the pins of PINS.sha256.

  pins.py [--lakefile F] [--manifest F] [--packages DIR] [--model-root DIR]

Checks, in order: lean-toolchain names the pinned Lean; lakefile.toml requires VCV-io and
Mathlib by git at the pinned revisions; lake-manifest.json resolves them to the same URLs and
revisions, and VCV-io's own manifest pins the same Mathlib; when lake has fetched them
(DIR, default .lake/packages), each checkout is at its revision and the VCV-io tree has no
tracked change and no untracked file that its .gitignore does not cover; and the three model
files (paths relative to the package, read under --model-root, default the package) have
their pinned SHA-256. The options let scripts/controls.py point the checks at altered copies.
Prints the first failure as "PINS FAIL: ..." and exits 1.
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent


def fail(msg):
    print(f'PINS FAIL: {msg}')
    sys.exit(1)


def main():
    a = sys.argv[1:]
    opt = lambda k, d: Path(a[a.index(k) + 1]) if k in a else d
    lakefile = opt('--lakefile', PKG / 'lakefile.toml')
    manifest = opt('--manifest', PKG / 'lake-manifest.json')
    packages = opt('--packages', PKG / '.lake' / 'packages')
    model_root = opt('--model-root', PKG)
    text = (PKG / 'PINS.sha256').read_text()
    pin = dict(re.findall(r'^# (\w+) (\S+)$', text, re.M))
    if (PKG / 'lean-toolchain').read_text().strip() != f"leanprover/lean4:{pin['lean']}":
        fail(f"lean-toolchain is not leanprover/lean4:{pin['lean']}")
    lf = lakefile.read_text()
    for name, key in (('VCVio', 'vcvio'), ('mathlib', 'mathlib')):
        block = re.search(r'\[\[require\]\]\s*name = "%s"\s*git = "([^"]+)"\s*rev = "([^"]+)"' % name, lf)
        if not block or block.groups() != (pin[f'{key}_url'], pin[f'{key}_rev']):
            fail(f'lakefile.toml does not require {name} at {pin[key + "_url"]} {pin[key + "_rev"]}')
    m = {p['name']: p for p in json.loads(manifest.read_text())['packages']}
    for name, key in (('VCVio', 'vcvio'), ('mathlib', 'mathlib')):
        p = m.get(name, {})
        if (p.get('url'), p.get('rev')) != (pin[f'{key}_url'], pin[f'{key}_rev']):
            fail(f"lake-manifest.json resolves {name} to {p.get('url')} {p.get('rev')}, "
                 f"not {pin[key + '_url']} {pin[key + '_rev']}")
    print(f"pins: lakefile.toml and lake-manifest.json require VCV-io {pin['vcvio_rev'][:8]} "
          f"and Mathlib {pin['mathlib_rev'][:8]}")
    vc = packages / 'VCVio'
    if vc.is_dir():
        for name, key in (('VCVio', 'vcvio'), ('mathlib', 'mathlib')):
            head = subprocess.run(['git', '-C', str(packages / name), 'rev-parse', 'HEAD'],
                                  capture_output=True, text=True).stdout.strip()
            if head != pin[f'{key}_rev']:
                fail(f'{packages / name} is at {head!r}, not {pin[key + "_rev"]}')
        vm = {p['name']: p['rev'] for p in json.loads((vc / 'lake-manifest.json').read_text())['packages']}
        if vm.get('mathlib') != pin['mathlib_rev']:
            fail(f"VCV-io's lake-manifest.json pins Mathlib {vm.get('mathlib')}, not {pin['mathlib_rev']}")
        dirty = subprocess.run(['git', '-C', str(vc), 'status', '--porcelain', '--untracked-files=all'],
                               capture_output=True, text=True).stdout.strip()
        if dirty:
            fail(f'the VCV-io checkout has changes: {dirty.splitlines()[0]}')
        print('pins: the VCV-io and Mathlib checkouts are at their revisions; the VCV-io tree is clean')
    else:
        print('pins: no fetched packages yet; checkouts not checked')
    for sha, path in re.findall(r'^([0-9a-f]{64})  (\S+)$', text, re.M):
        f = model_root / path
        got = hashlib.sha256(f.read_bytes()).hexdigest() if f.is_file() else 'missing'
        if got != sha:
            fail(f'model file {path} has sha256 {got}, not the pinned {sha}')
    print('pins: the three model files (State.lean, Tx.lean, Events.lean) match PINS.sha256')


if __name__ == '__main__':
    main()
