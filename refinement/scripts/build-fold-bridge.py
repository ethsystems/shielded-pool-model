#!/usr/bin/env python3
"""Build the fold bridge (fold-bridge/) in the Lean workspace of ../circuits-lampe.

  build-fold-bridge.py [--jobs N]

1. In ../circuits-lampe (or $CIRCUITS_LAMPE): `lake exe cache get`, `lake build` of Lampe, its
   stdlib and the extracted circuit packages, then its own `scripts/build.py --jobs N` for the
   proof modules the bridge imports (`Merkle.Fold`, `Withdraw.Root`, `Transfer.Root`,
   `Transfer.Execution` and their imports). This writes only build outputs of that package
   (`.lake/`, `build/`), as its own check does.
2. The modules of fold-bridge/ and every module of this repository they import (the model files
   of ../LeanShieldedPool/, unchanged, and the refinement modules of this package) are compiled
   from their sources, in import order, into build/fold-bridge/lib with `lake -d
   <circuits-lampe> env lean` and the flags of the circuits-lampe proof modules. A module is
   skipped when its source, the flags and its imports are unchanged since its last compile.

Logs: build/fold-bridge/ (lake.log, build.log, <module>.log, times.tsv: module, exit code,
seconds, peak RSS in KiB).
"""
import hashlib
import os
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from targets import FB, FB_FLAGS, FB_OUT, PKG, ROOT, circuits_lampe  # noqa: E402

LOGS = PKG / 'build' / 'fold-bridge'
CL_MODULES = ['Merkle.Fold', 'Withdraw.Root', 'Transfer.Root', 'Transfer.Execution']
CL_TARGETS = ['Lampe', '«std-1.0.0-beta.21»', '«poseidon-0.0.0»', '«binary_merkle_root-0.0.0»',
              '«deposit-0.0.0»', '«withdraw-0.0.0»', '«transfer-0.0.0»']


def source(module):
    """(directory the module path is relative to, the source file), or None (not ours)."""
    rel = Path(*module.split('.')).with_suffix('.lean')
    for base in (FB, PKG, ROOT):
        if base == ROOT and module.split('.')[0] != 'LeanShieldedPool':
            continue
        if (base / rel).is_file():
            return base, base / rel
    return None


def imports(path):
    return re.findall(r'^import\s+(\S+)', path.read_text(), re.M)


def step(name, argv, cwd, log, env=None):
    t = time.monotonic()
    with open(log, 'w') as f:
        ec = subprocess.run(argv, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env).returncode
    print(f'{name}: exit {ec}, {time.monotonic() - t:.0f}s', flush=True)
    if ec != 0:
        print(''.join(open(log).readlines()[-15:]))
        sys.exit(f'BUILD FAIL (fold bridge): {name} ({log.relative_to(PKG)})')


def main():
    args = sys.argv[1:]
    jobs = int(args[1]) if args[:1] == ['--jobs'] else 1
    cl = circuits_lampe()
    LOGS.mkdir(parents=True, exist_ok=True)
    FB_OUT.mkdir(parents=True, exist_ok=True)
    step('circuits-lampe: lake exe cache get', ['lake', 'exe', 'cache', 'get'], cl, LOGS / 'cache.log')
    step('circuits-lampe: lake build of Lampe and the extracted packages', ['lake', 'build', *CL_TARGETS],
         cl, LOGS / 'lake.log')
    step('circuits-lampe: scripts/build.py ' + ' '.join(CL_MODULES),
         [sys.executable, 'scripts/build.py', '--jobs', str(jobs), *CL_MODULES], cl, LOGS / 'build.log')

    roots = ['FoldBridge.' + f.stem for f in sorted((FB / 'FoldBridge').glob('*.lean'))]
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        src = source(m)
        if src is None:
            return
        for i in imports(src[1]):
            visit(i)
        order.append(m)
    for r in roots:
        visit(r)
    mods = [m for m in order if source(m)]
    env = {**os.environ, 'LEAN_PATH': str(FB_OUT)}
    key = {}
    times = open(LOGS / 'times.tsv', 'a')
    built = 0
    for m in mods:
        base, src = source(m)
        deps = [i for i in imports(src) if i in key]
        h = hashlib.sha256(src.read_bytes() + ' '.join(FB_FLAGS).encode()
                           + ''.join(key[d] for d in sorted(deps)).encode()).hexdigest()
        key[m] = h
        olean = FB_OUT / Path(*m.split('.')).with_suffix('.olean')
        trace = olean.with_suffix('.trace-cl')
        if olean.exists() and trace.exists() and trace.read_text() == h:
            continue
        olean.parent.mkdir(parents=True, exist_ok=True)
        argv = ['lake', '-d', str(cl), 'env', 'lean', *FB_FLAGS, '-o', str(olean),
                '-i', str(olean.with_suffix('.ilean')), str(src.relative_to(base))]
        t = time.monotonic()
        with open(LOGS / f'{m}.log', 'w') as f:
            p = subprocess.Popen(argv, cwd=base, env=env, stdout=f, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(p.pid, 0)
        ec = os.waitstatus_to_exitcode(status)
        secs = time.monotonic() - t
        times.write(f'{m}\t{ec}\t{secs:.1f}\t{usage.ru_maxrss}\n')
        times.flush()
        if ec != 0:
            first = next((l for l in (LOGS / f'{m}.log').read_text().splitlines() if 'error' in l), '')
            sys.exit(f'BUILD FAIL (fold bridge): {m} exit {ec}: {first[:200]}')
        trace.write_text(h)
        built += 1
        print(f'ok   {m} {secs:.1f}s', flush=True)
    print(f'BUILD PASS (fold bridge): {len(mods)} modules ({built} compiled), '
          f'{sum(1 for m in mods if m.startswith("FoldBridge."))} of them in fold-bridge/')


if __name__ == '__main__':
    main()
