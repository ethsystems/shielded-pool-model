#!/usr/bin/env python3
"""Compile the proof modules of this package with `lake env lean`, in import order.

  build.py [--jobs N] [MODULE...]   build MODULE and its imports (default: every module)

Each module is compiled once with the flags below, the flags of the original runs. A module
is skipped when its source, its flags, the hashes of the package modules it imports and the
fingerprint of its dependencies are unchanged since its last successful compile (the
`.trace-cl` file next to its olean). The fingerprint covers lakefile.toml, lake-manifest.json,
lean-toolchain, PINS.sha256, every olean of the five extracted packages, and the commit and
uncommitted changes of the Lampe and stdlib checkouts; when any of them changes, every proof
module is compiled again. The
extracted packages, Lampe and its stdlib must be built first (`lake build` of their
targets; scripts/check.sh does that). Every compile is logged to build/logs/<module>.log,
and build/times.tsv gets one row per compile: module, exit code, seconds, peak RSS (KiB).
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
FLAGS = ['-M8192', '--tstack=65536', '-DElab.async=false', '-DmaxRecDepth=10000',
         '-DmaxHeartbeats=4000000']
SKIP_DIRS = {'controls', 'extracted', 'scripts', 'build', '.lake', '.lampe'}
OUT = PKG / '.lake' / 'build' / 'lib' / 'lean'
LOGS = PKG / 'build' / 'logs'


def modules():
    mods = {}
    for f in PKG.rglob('*.lean'):
        rel = f.relative_to(PKG)
        if rel.parts[0] in SKIP_DIRS or rel.name == 'Census.lean':
            continue
        mods['.'.join(rel.with_suffix('').parts)] = f
    return mods


def imports(path):
    return re.findall(r'^import\s+(\S+)', path.read_text(), re.M)


def checkout_state(d):
    """The commit and the uncommitted changes of a git checkout (or of its enclosing repo)."""
    g = lambda *a: subprocess.run(['git', '-C', str(d), *a], capture_output=True).stdout
    return g('rev-parse', 'HEAD') + g('diff', 'HEAD', '--', '.') + g('status', '--porcelain', '--', '.')


def fingerprint():
    """A hash of everything outside the proof modules that a compile reads."""
    h = hashlib.sha256()
    for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'PINS.sha256'):
        h.update(name.encode() + (PKG / name).read_bytes())
    ext = PKG / 'extracted'
    oleans = sorted(ext.glob('*/.lake/build/lib/lean/**/*.olean')) + \
        sorted(ext.glob('deps/*/.lake/build/lib/lean/**/*.olean'))
    if not oleans:
        sys.exit('no olean of the extracted packages: build them first (scripts/check.sh)')
    for f in oleans:
        h.update(str(f.relative_to(PKG)).encode() + hashlib.sha256(f.read_bytes()).digest())
    m = json.loads((PKG / 'lake-manifest.json').read_text())
    for p in m['packages']:
        if p['name'].strip('«»') in ('Lampe', 'std-1.0.0-beta.21'):
            if p['type'] == 'path':
                d = PKG / p['dir']
            else:
                d = PKG / m.get('packagesDir', '.lake/packages') / p['name'].strip('«»')
                d = d / (p.get('subDir') or '')
            h.update(p['name'].encode() + checkout_state(d))
    return h.hexdigest()


def main():
    args = sys.argv[1:]
    jobs = 1
    if args[:1] == ['--jobs']:
        jobs, args = int(args[1]), args[2:]
    mods = modules()
    deps = {m: [i for i in imports(f) if i in mods] for m, f in mods.items()}
    wanted, stack = set(), list(args or mods)
    while stack:
        m = stack.pop()
        if m not in mods:
            sys.exit(f'unknown module {m}')
        if m not in wanted:
            wanted.add(m)
            stack.extend(deps[m])
    LOGS.mkdir(parents=True, exist_ok=True)
    times = open(PKG / 'build' / 'times.tsv', 'a')
    key, done, failed, running = {}, set(), set(), {}
    env = {**os.environ, 'LEAN_NUM_THREADS': os.environ.get('LEAN_NUM_THREADS', '1')}
    skipped = built = 0
    fp = fingerprint()
    while len(done) + len(failed) < len(wanted):
        ready = [m for m in sorted(wanted - done - failed - set(running))
                 if all(d in done for d in deps[m])]
        blocked = [m for m in sorted(wanted - done - failed - set(running))
                   if any(d in failed for d in deps[m])]
        for m in blocked:
            failed.add(m)
            print(f'SKIP {m}: an import failed', flush=True)
        for m in ready:
            if len(running) >= jobs:
                break
            h = hashlib.sha256(mods[m].read_bytes() + ' '.join(FLAGS).encode() + fp.encode()
                               + ''.join(key[d] for d in sorted(deps[m])).encode()).hexdigest()
            key[m] = h
            olean = OUT / Path(*m.split('.')).with_suffix('.olean')
            trace = olean.with_suffix('.trace-cl')
            if olean.exists() and trace.exists() and trace.read_text() == h:
                done.add(m)
                skipped += 1
                continue
            olean.parent.mkdir(parents=True, exist_ok=True)
            log = open(LOGS / f'{m}.log', 'w')
            cmd = ['lake', 'env', 'lean', *FLAGS, '-o', str(olean), '-i',
                   str(olean.with_suffix('.ilean')), str(mods[m].relative_to(PKG))]
            p = subprocess.Popen(cmd, cwd=PKG, env=env, stdout=log, stderr=subprocess.STDOUT)
            running[m] = (p, time.monotonic(), trace, h)
        if not running:
            continue
        pid, status, usage = os.wait4(-1, 0)
        m = next(k for k, v in running.items() if v[0].pid == pid)
        p, start, trace, h = running.pop(m)
        ec = os.waitstatus_to_exitcode(status)
        secs = time.monotonic() - start
        times.write(f'{m}\t{ec}\t{secs:.1f}\t{usage.ru_maxrss}\n')
        times.flush()
        if ec == 0:
            trace.write_text(h)
            done.add(m)
            built += 1
            print(f'ok   {m} {secs:.1f}s', flush=True)
        else:
            failed.add(m)
            first = next((l for l in (LOGS / f'{m}.log').read_text().splitlines() if 'error' in l), '')
            print(f'FAIL {m} exit {ec} {secs:.1f}s {first[:200]}', flush=True)
    print(f'BUILD {"FAIL" if failed else "PASS"}: {built} compiled, {skipped} up to date, '
          f'{len(failed)} failed or skipped', flush=True)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
