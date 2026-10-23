#!/usr/bin/env python3
"""Check the Poseidon round constants against the extracted `Consts.lean`.

  gen-constants3.py   parse `x5_2_config`, `x5_3_config` and `x5_5_config` from the extracted
                      poseidon Consts.lean and check that Poseidon/Constants{2,3,5}.lean define
                      `rc`, `mds`, `pre` and `sparse` with exactly these values

The parser reads the literal arguments of each config call (`N` round constants, the `T x T`
MDS matrix, the `T x T` pre-sparse matrix and `X` sparse-matrix entries). Width 3 is the one
this package derived from the extracted file; widths 2 and 5 check the parser.
"""
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
CONSTS = PKG / 'extracted/deps/poseidon-0.0.0/poseidon-0.0.0/Extracted/Poseidon/Bn254/Consts.lean'


def parse(lines, name, T, N, X):
    i = next(k for k, l in enumerate(lines)
             if l.startswith(f'noir_def «poseidon-0.0.0»::poseidon::bn254::consts::{name}<>'))
    line = lines[i + 1]
    tail = line[line.index('consts::alpha<> as λ() -> Field)()'):]
    nums = [int(x) for x in re.findall(r'\((-?\d+): Field\)', tail)]
    assert len(nums) == N + 2 * T * T + X, (name, len(nums))
    rc = nums[:N]
    mds = [nums[N + T * r: N + T * r + T] for r in range(T)]
    pre = [nums[N + T * T + T * r: N + T * T + T * r + T] for r in range(T)]
    return rc, mds, pre, nums[N + 2 * T * T:]


def vec(xs):
    return '⟨[' + ','.join(str(x) for x in xs) + '],rfl⟩'


def mat(m):
    return '⟨[' + ','.join(vec(r) for r in m) + '],rfl⟩'


def main():
    lines = CONSTS.read_text().splitlines()
    bad = 0
    for T, N, X in ((2, 72, 168), (3, 81, 285), (5, 100, 540)):
        rc, mds, pre, sp = parse(lines, f'x5_{T}_config', T, N, X)
        src = (PKG / 'Poseidon' / f'Constants{T}.lean').read_text()
        want = [f'def rc : List.Vector (Fp p) {N} := {vec(rc)}',
                f'def mds : List.Vector (List.Vector (Fp p) {T}) {T} := {mat(mds)}',
                f'def pre : List.Vector (List.Vector (Fp p) {T}) {T} := {mat(pre)}',
                f'def sparse : List.Vector (Fp p) {X} := {vec(sp)}']
        for w in want:
            if w not in src:
                bad += 1
                print(f'CONSTANTS DIFFER: width {T}: {w[:60]}...')
    if bad:
        print(f'CONSTANTS CHECK FAIL: {bad}')
        sys.exit(1)
    print('CONSTANTS CHECK PASS: widths 2, 3 and 5 equal the extracted Consts.lean')


if __name__ == '__main__':
    main()
