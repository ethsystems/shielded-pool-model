#!/usr/bin/env python3
"""Check (or write) PINS.sha256: the files outside this package that its results rest on.

  pins.py           check every pinned file, and that the pinned model files are exactly the
                    import closure of this package's modules in ../LeanShieldedPool
  pins.py --write   write PINS.sha256 from the current files (after a reviewed change)

Pinned: the model modules of the parent directory that the package imports, directly or through
each other (the refinement is a statement about these files); the parent's lakefile.toml,
lake-manifest.json and lean-toolchain (Lean 4.33.1, Mathlib); this package's own toolchain and
manifest; and, for the fold bridge, the circuits-lampe modules it imports and that package's
lakefile.toml and PINS.sha256 (which pin Lampe and the extracted circuits).
"""
import hashlib
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ROOT = PKG.parent
PINS = PKG / 'PINS.sha256'
GROUPS = ['Refinement', 'Tree', 'Balance', 'Journey', 'Gas', 'fold-bridge/FoldBridge']
CL_FILES = ['circuits-lampe/lakefile.toml', 'circuits-lampe/PINS.sha256',
            'circuits-lampe/Merkle/Fold.lean', 'circuits-lampe/Withdraw/Root.lean',
            'circuits-lampe/Transfer/Root.lean', 'circuits-lampe/Transfer/Execution.lean']
FIXED = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
         'refinement/lean-toolchain', 'refinement/lake-manifest.json']


def model_closure():
    todo = [i for g in GROUPS for f in (PKG / g).rglob('*.lean')
            for i in re.findall(r'^import\s+(LeanShieldedPool\.\S+)', f.read_text(), re.M)]
    seen = set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        f = ROOT / Path(*m.split('.')).with_suffix('.lean')
        todo += re.findall(r'^import\s+(LeanShieldedPool\.\S+)', f.read_text(), re.M)
    return sorted(str(Path(*m.split('.')).with_suffix('.lean')) for m in seen)


def sha(p):
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()


def main():
    model = model_closure()
    files = model + FIXED + CL_FILES
    if sys.argv[1:] == ['--write']:
        lines = ['# Pins of the refinement package: sha256 of each file outside the package that its',
                 '# results rest on, relative to the repository root. Checked by scripts/pins.py.',
                 '# The LeanShieldedPool/ lines are the model modules the package imports, directly or',
                 '# through each other: the refinement theorems are statements about these files.']
        lines += [f'{sha(p)}  {p}' for p in files]
        PINS.write_text('\n'.join(lines) + '\n')
        print(f'wrote {PINS.name}: {len(files)} files ({len(model)} model modules)')
        return
    bad = []
    pinned = {}
    for l in PINS.read_text().splitlines():
        if l and not l.startswith('#'):
            h, p = l.split('  ', 1)
            pinned[p] = h
    pinned_model = sorted(p for p in pinned if p.startswith('LeanShieldedPool/'))
    if pinned_model != model:
        bad.append(f'the pinned model modules are not the import closure: '
                   f'{sorted(set(pinned_model) ^ set(model))}')
    for p in sorted(set(files) - set(pinned)):
        bad.append(f'not pinned: {p}')
    for p, h in sorted(pinned.items()):
        if not (ROOT / p).is_file():
            bad.append(f'missing: {p}')
        elif sha(p) != h:
            bad.append(f'differs from its pin: {p}')
    if bad:
        for b in bad:
            print('PINS', b)
        sys.exit(f'PINS FAIL: {len(bad)} problems')
    print(f'PINS PASS: {len(pinned)} files, {len(model)} of them the model modules the package imports')


if __name__ == '__main__':
    main()
