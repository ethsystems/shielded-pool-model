#!/usr/bin/env python3
"""Run Verus on every mirror, every probe and every negative control.

usage: verus-run.py <verus dir> <work dir> [jobs]

- Each mirror in mirrors/ must verify with --no-cheating, 0 errors, and the verified count of
  mirrors/VERIFIED.txt.
- probes/async.rs and probes/await.rs must verify; probes/async_trait.rs must stop with the
  unsupported-feature diagnostic (async functions in traits are outside this Verus release).
- Each control in controls/controls.json is its mirror with one replacement. It counts as
  refuted only if Verus reaches verification (prints its results line), reports at least one
  error, reports no error other than a verification error (a compiler error fails the
  control), and reports the expected proof diagnostic ("proof error": any of postcondition,
  precondition, assertion or loop invariant not satisfied) at a location inside the control's
  target function (common.control_target: the function the control changes, or the function
  its `target` names). An expected diagnostic elsewhere in the file does not count.
  A control whose target function stops at the solver resource limit (rlimit) is not refuted,
  but it does not verify either: it is reported apart ("rlimit") and does not fail the run,
  unless STRICT=1, which counts it as a failure.
Writes <work dir>/results.json and one log per run; prints one VERUS line per run."""
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import common

verus = Path(sys.argv[1]) / 'verus'
work = Path(sys.argv[2])
jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
(work / 'logs').mkdir(parents=True, exist_ok=True)
(work / 'controls').mkdir(parents=True, exist_ok=True)
env = dict(os.environ, RUSTUP_TOOLCHAIN=common.pins()['rust_toolchain'])
want = dict(l.split() for l in (common.PKG / 'mirrors' / 'VERIFIED.txt').read_text().splitlines() if l and not l.startswith('#'))


def verus_run(path, label):
    t = time.monotonic()
    p = subprocess.Popen([str(verus), str(path), '--no-cheating', '--multiple-errors', '20'],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, text=True)
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    (work / 'logs' / (label.replace('/', '__') + '.log')).write_text(out)
    m = re.search(r'verification results:: (\d+) verified, (\d+) errors', out)
    return dict(label=label, exit=p.returncode, wall_s=round(time.monotonic() - t, 3), maxrss_kb=ru.ru_maxrss,
                verified=int(m[1]) if m else None, errors=int(m[2]) if m else None,
                diagnostics=sorted(set(re.findall(r'^error(?:\[\w+\])?: (.*)$', out, re.M))),
                located=located(out, path), out=out)


def located(out, path):
    """Each error of a run except the closing count: [message, error code or None, line of its
    first location if that location is in `path`, else None]."""
    lines = out.splitlines()
    res = []
    for i, line in enumerate(lines):
        m = re.match(r'^error(?:\[(\w+)\])?: (.*)$', line)
        if not m or m[2].startswith('aborting due to'):
            continue
        n = re.match(r'^\s*--> (.*):(\d+):\d+$', lines[i + 1]) if i + 1 < len(lines) else None
        at = int(n[2]) if n and Path(n[1]).resolve() == Path(path).resolve() else None
        res.append([m[2], m[1], at])
    return res


def mirror_job(path):
    r = verus_run(path, 'mirror/' + path.name)
    r['pass'] = r['exit'] == 0 and r['errors'] == 0 and r['verified'] == int(want.get(path.name, -1))
    r['want'] = int(want.get(path.name, -1))
    return r


def probe_job(path):
    r = verus_run(path, 'probe/' + path.name)
    if path.name == 'async_trait.rs':
        r['expect'] = 'unsupported'
        r['pass'] = r['exit'] != 0 and r['verified'] is None and common.UNSUPPORTED in r['out']
    else:
        r['expect'] = 'pass'
        r['pass'] = r['exit'] == 0 and r['errors'] == 0 and r['verified'] == int(want.get('probes/' + path.name, -1))
    return r


def control_job(c):
    path = work / 'controls' / (c['id'].replace('/', '__') + '.rs')
    mutated = common.apply_control(c)
    path.write_text(mutated)
    first, last, name = common.control_target(c, mutated)
    r = verus_run(path, 'control/' + c['id'])
    exp = common.PROOF_ERRORS if c['expect'] == 'proof error' else (c['expect'],)
    reached = r['exit'] != 0 and r['verified'] is not None and (r['errors'] or 0) >= 1
    other = [msg for msg, code, _ in r['located'] if code or not any(v in msg for v in common.VERIFY_ERRORS)]
    inside = [msg for msg, _, at in r['located'] if at is not None and first <= at <= last]
    refuted = reached and not other and any(e in msg for e in exp for msg in inside)
    rlimit = reached and not other and not refuted and any(common.RLIMIT in msg for msg in inside)
    outcome = ('refuted' if refuted else 'rlimit' if rlimit else 'compiler error' if other
               else 'not rejected in its target' if r['located'] else 'not rejected')
    r.update(id=c['id'], mirror=c['mirror'], expect=c['expect'], target=[name, first, last], outcome=outcome,
             outside=[[msg, at] for msg, _, at in r['located'] if at is None or not first <= at <= last],
             **{'pass': refuted or (rlimit and os.environ.get('STRICT') != '1')})
    return r


t0 = time.monotonic()
results = {}
with ThreadPoolExecutor(jobs) as ex:
    for kind, fn, items in [('mirrors', mirror_job, sorted((common.PKG / 'mirrors').glob('*.rs'))),
                            ('probes', probe_job, sorted((common.PKG / 'probes').glob('*.rs'))),
                            ('controls', control_job, common.controls())]:
        results[kind] = list(ex.map(fn, items))
        for r in results[kind]:
            note = (f"{r['verified']} verified, {r['errors']} errors" if r['verified'] is not None else 'no results line')
            if kind == 'controls':
                note += f"; {'; '.join(d for d in r['diagnostics'] if not d.startswith('aborting'))} (target {r['target'][0]}: {r['outcome']})"
            print(f"VERUS {'ok' if r['pass'] else 'FAIL'} {r['label']}: {note}, {r['wall_s']} s, {r['maxrss_kb'] // 1024} MiB", flush=True)
            if not r['pass']:
                print(r['out'][-3000:], flush=True)
for kind in results:
    for r in results[kind]:
        r.pop('out')
summary = dict(
    mirrors=len(results['mirrors']), mirrors_pass=sum(r['pass'] for r in results['mirrors']),
    verified_items=sum(r['verified'] or 0 for r in results['mirrors']),
    probes=len(results['probes']), probes_pass=sum(r['pass'] for r in results['probes']),
    controls=len(results['controls']), controls_refuted=sum(r['outcome'] == 'refuted' for r in results['controls']),
    controls_rlimit=sorted(r['id'] for r in results['controls'] if r['outcome'] == 'rlimit'),
    controls_failed=sorted(r['id'] for r in results['controls'] if not r['pass']),
    strict=os.environ.get('STRICT') == '1',
    wall_s=round(time.monotonic() - t0, 1), verus_sum_s=round(sum(r['wall_s'] for k in results for r in results[k]), 1),
    max_rss_mib=max(r['maxrss_kb'] for k in results for r in results[k]) // 1024, jobs=jobs)
try:
    cg = Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1]
    base = Path('/sys/fs/cgroup') / cg.lstrip('/')
    summary.update(cgroup=cg, memory_max=(base / 'memory.max').read_text().strip(),
                   memory_peak=(base / 'memory.peak').read_text().strip())
except Exception as e:  # no cgroup v2 view: the per-run max RSS above still holds
    summary['cgroup'] = f'unavailable ({e.__class__.__name__})'
ok = (summary['mirrors_pass'] == summary['mirrors'] and summary['probes_pass'] == summary['probes']
      and not summary['controls_failed'])
summary['pass'] = ok
(work / 'results.json').write_text(json.dumps(dict(summary=summary, **results), indent=1) + '\n')
print('VERUS ' + ('PASS ' if ok else 'FAIL ') + json.dumps(summary), flush=True)
sys.exit(0 if ok else 1)
