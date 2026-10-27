#!/usr/bin/env python3
"""Build the fold bridge (fold-bridge/) in the Lean workspace of ../circuits-lampe.

  build-fold-bridge.py [--jobs N]

1. In ../circuits-lampe: `lake exe cache get` (which also clones Lampe and its stdlib), then the
   dependency check of scripts/pins.py (every git package of that package's manifest checked
   out at its manifest rev, unchanged, no untracked file), `lake build` of Lampe, its stdlib and
   the extracted circuit packages, then its own `scripts/build.py --jobs N` for the proof modules
   the bridge imports (`Merkle.Fold`, `Withdraw.Root`, `Transfer.Root`, `Transfer.Execution` and
   their imports). This writes only build outputs of that package (`.lake/`, `build/`), as its
   own check does. scripts/build.py skips a module whose source and imports are unchanged; it
   does not see Lampe, the extracted packages or the compiler. So when any of these differs
   from the last run of this script (the Lean githash, and the pinned lakefiles, manifest,
   toolchain and extracted sources of circuits-lampe), its `.trace-cl` files are removed first
   and every module is compiled again.
2. No module of this repository may also have an olean in the circuits-lampe workspace: lake
   puts that workspace first on LEAN_PATH, so such an olean would be loaded in its place.
3. The modules of fold-bridge/ and every module of this repository they import (the model files
   of ../LeanShieldedPool/, unchanged, and the refinement modules of this package) are compiled
   from their sources, in import order, into build/fold-bridge/lib with `lake -d
   ../circuits-lampe env lean` and the flags of the circuits-lampe proof modules. The directory
   is emptied first: every module is compiled on every run.

Logs: build/fold-bridge/ (lake.log, build.log, <module>.log, times.tsv: module, exit code,
seconds, peak RSS in KiB).
"""
import hashlib
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pins  # noqa: E402
from targets import CL, FB, FB_FLAGS, FB_OUT, PKG  # noqa: E402

LOGS = PKG / 'build' / 'fold-bridge'
CL_MODULES = ['Merkle.Fold', 'Withdraw.Root', 'Transfer.Root', 'Transfer.Execution']
CL_TARGETS = ['Lampe', '«std-1.0.0-beta.21»', '«poseidon-0.0.0»', '«binary_merkle_root-0.0.0»',
              '«deposit-0.0.0»', '«withdraw-0.0.0»', '«transfer-0.0.0»']


def source(module):
    """(directory the module path is relative to, the source file), or None (not ours)."""
    rel = Path(*module.split('.')).with_suffix('.lean')
    for base in (FB, PKG, pins.ROOT):
        if base == pins.ROOT and module.split('.')[0] != 'LeanShieldedPool':
            continue
        if (base / rel).is_file():
            return base, base / rel
    return None


def step(name, argv, cwd, log, env=None):
    t = time.monotonic()
    with open(log, 'w') as f:
        ec = subprocess.run(argv, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env).returncode
    print(f'{name}: exit {ec}, {time.monotonic() - t:.0f}s', flush=True)
    if ec != 0:
        print(''.join(open(log).readlines()[-15:]))
        sys.exit(f'BUILD FAIL (fold bridge): {name} ({log.relative_to(PKG)})')


def deps(when):
    n, bad = pins.check_deps('fold-bridge')
    for b in bad:
        print('DEPS', b)
    if bad:
        sys.exit(f'BUILD FAIL (fold bridge): {when}, a circuits-lampe dependency differs from its manifest')
    print(f'circuits-lampe dependencies ({when}): {n} git packages at their manifest revs, unchanged, '
          f'no untracked files', flush=True)


def outside_state():
    """A hash of what the circuits-lampe proof modules read besides their own sources."""
    lean = subprocess.run(['lake', '-d', str(CL), 'env', 'lean', '--githash'], capture_output=True,
                          text=True, check=True).stdout
    lines = [l for l in pins.PINS.read_text().splitlines()
             if l.split('  ')[-1].startswith(('circuits-lampe/extracted/', 'circuits-lampe/lake'))
             or l.endswith('circuits-lampe/lean-toolchain')]
    return hashlib.sha256((lean + '\n'.join(lines)).encode()).hexdigest()


def shadowed(mods):
    env = {k: v for k, v in os.environ.items() if k != 'LEAN_PATH'}
    path = subprocess.run(['lake', '-d', str(CL), 'env', 'printenv', 'LEAN_PATH'], env=env,
                          capture_output=True, text=True, check=True).stdout.strip().split(':')
    return [f'{m} ({d})' for m in mods for d in path if d
            and (Path(d) / Path(*m.split('.'))).with_suffix('.olean').exists()]


def main():
    args = sys.argv[1:]
    jobs = int(args[1]) if args[:1] == ['--jobs'] else 1
    LOGS.mkdir(parents=True, exist_ok=True)
    step('circuits-lampe: lake exe cache get', ['lake', 'exe', 'cache', 'get'], CL, LOGS / 'cache.log')
    deps('after the fetch')
    step('circuits-lampe: lake build of Lampe and the extracted packages', ['lake', 'build', *CL_TARGETS],
         CL, LOGS / 'lake.log')
    stamp, state = LOGS / 'circuits-lampe-state', outside_state()
    if not stamp.exists() or stamp.read_text() != state:
        traces = list((CL / '.lake' / 'build' / 'lib' / 'lean').rglob('*.trace-cl'))
        for t in traces:
            t.unlink()
        print(f'circuits-lampe: outside state differs from the last run; {len(traces)} .trace-cl '
              f'files removed', flush=True)
        stamp.unlink(missing_ok=True)
    step('circuits-lampe: scripts/build.py ' + ' '.join(CL_MODULES),
         [sys.executable, 'scripts/build.py', '--jobs', str(jobs), *CL_MODULES], CL, LOGS / 'build.log')
    stamp.write_text(state)
    deps('after the build')

    roots = ['FoldBridge.' + f.stem for f in sorted((FB / 'FoldBridge').glob('*.lean'))]
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        src = source(m)
        if src is None:
            return
        for i in pins.imports(src[1]):
            visit(i)
        order.append(m)
    for r in roots:
        visit(r)
    mods = [m for m in order if source(m)]
    bad = shadowed(mods)
    if bad:
        sys.exit(f'BUILD FAIL (fold bridge): an olean in the circuits-lampe workspace would shadow {bad[:5]}')
    shutil.rmtree(FB_OUT, ignore_errors=True)
    FB_OUT.mkdir(parents=True)
    env = {**os.environ, 'LEAN_PATH': str(FB_OUT)}
    times = open(LOGS / 'times.tsv', 'a')
    for m in mods:
        base, src = source(m)
        olean = FB_OUT / Path(*m.split('.')).with_suffix('.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        argv = ['lake', '-d', str(CL), 'env', 'lean', *FB_FLAGS, '-o', str(olean),
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
        print(f'ok   {m} {secs:.1f}s', flush=True)
    print(f'BUILD PASS (fold bridge): {len(mods)} modules compiled, '
          f'{sum(1 for m in mods if m.startswith("FoldBridge."))} of them in fold-bridge/')


if __name__ == '__main__':
    main()
