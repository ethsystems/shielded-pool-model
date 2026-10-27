#!/usr/bin/env python3
"""The mirrors against the pinned source.

usage: source-check.py <pocs checkout> [--write-diffs]

1. pocs holds the pinned commit, and the 13 client files there have the pinned blob ids.
2. Each of the 110 regions of source/manifest.json, read from those blobs, has its sha256.
3. For each of the 96 Verus rows, the unified diff of the source region against the mirrored
   function equals diffs/<n>-<name>.diff (--write-diffs writes them instead).
4. No mirror holds a local admission: assume, admit, external_body, assume_specification,
   external_fn_specification, external_type_specification, uninterp, verifier::external.
5. The code lines of each mirror and probe (comment lines removed) have the sha256 of
   scripts/origins.txt: the files differ from their first checked form in comments only.
6. Every control's replacement text occurs exactly once where it applies.
Prints one SOURCE line per step; exit 1 on any failure."""
import difflib
import hashlib
import re
import subprocess
import sys
from pathlib import Path

import common

pocs = Path(sys.argv[1])
write = '--write-diffs' in sys.argv
P = common.pins()
M = common.manifest()
commit, prefix = P['pocs_commit'], P['pocs_dir'].rstrip('/') + '/'
ok = True


def report(step, good, msg):
    global ok
    ok &= good
    print(f"SOURCE {'ok' if good else 'FAIL'} {step}: {msg}", flush=True)


def git(*a):
    return subprocess.run(['git', '-C', str(pocs), *a], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)


# 1. commit and blobs
if git('cat-file', '-e', commit + '^{commit}').returncode:
    report('commit', False, f'{pocs} does not hold {commit}')
    sys.exit(1)
assert M['commit'] == commit and M['source_prefix'] == prefix
got = {}
for line in git('ls-tree', '-r', commit, prefix).stdout.decode().splitlines():
    meta, path = line.split('\t', 1)
    got[path[len(prefix):]] = meta.split()[2]
bad = [f'{p}: {got.get(p)} (pinned {b})' for b, p in P['blobs'] if got.get(p) != b]
report('blobs', not bad, f'{len(P["blobs"]) - len(bad)} of {len(P["blobs"])} files at {commit[:7]} have the pinned blob ids' + ('; ' + '; '.join(bad) if bad else ''))
files = {p: git('cat-file', 'blob', b).stdout.decode() for b, p in P['blobs']}

# 2. regions
rows = M['rows']
region = {}
bad = []
for r in rows:
    if r['file'] not in files:
        bad.append(f"{r['n']}: {r['file']} is not pinned")
        continue
    text = '\n'.join(files[r['file']].splitlines()[r['line'] - 1:r['end']]) + '\n'
    region[r['n']] = text
    if hashlib.sha256(text.encode()).hexdigest() != r['sha256']:
        bad.append(f"{r['n']} {r['function']} {r['file']}:{r['line']}-{r['end']}")
report('regions', not bad and len(rows) == 110, f'{len(rows) - len(bad)} of {len(rows)} source regions have their pinned sha256' + ('; ' + '; '.join(bad) if bad else ''))

# 3. diffs
ddir = common.PKG / 'diffs'
ddir.mkdir(exist_ok=True)
want, bad = set(), []
for r in rows:
    if not r['verus']:
        continue
    v = r['verus']
    mirror = common.fn_text(common.mirror_text(v['mirror']), v['marker'])
    name = re.sub(r'[^A-Za-z0-9]+', '_', r['function']).strip('_')
    path = ddir / f"{r['n']:03d}-{name}.diff"
    want.add(path.name)
    d = ''.join(difflib.unified_diff(region[r['n']].splitlines(True), mirror.splitlines(True),
                                     f"a04b8b3:{r['file']}:{r['line']}-{r['end']}", f"mirrors/{v['mirror']}"))
    if write:
        path.write_text(d)
    elif not path.exists() or path.read_text() != d:
        bad.append(path.name)
extra = sorted(p.name for p in ddir.glob('*.diff') if p.name not in want)
report('diffs', not bad and not extra, f'{len(want) - len(bad)} of {len(want)} source-to-mirror diffs equal diffs/'
       + ('; differ: ' + ', '.join(bad) if bad else '') + ('; extra: ' + ', '.join(extra) if extra else ''))

# 4. admissions
pat = re.compile(r'\bassume\s*\(|\badmit\s*\(|external_body|assume_specification|external_fn_specification'
                 r'|external_type_specification|\buninterp\b|verifier::external\b')
mirrors = sorted((common.PKG / 'mirrors').glob('*.rs'))
hits = [f'{p.name}:{n}' for p in mirrors for n, l in enumerate(p.read_text().splitlines(), 1) if pat.search(l)]
report('admissions', not hits, f'no local admission in {len(mirrors)} mirror files' if not hits else ', '.join(hits))

# 5. origins
bad, n = [], 0
for line in (common.PKG / 'scripts' / 'origins.txt').read_text().splitlines():
    if line.startswith('#'):
        continue
    path, _, code_sha = line.split()
    t = (common.PKG / path).read_text()
    code = ''.join(l for l in t.splitlines(True) if not l.lstrip().startswith('//'))
    n += 1
    if hashlib.sha256(code.encode()).hexdigest() != code_sha:
        bad.append(path)
report('origins', not bad and n == len(mirrors) + 3, f'{n - len(bad)} of {n} mirror and probe files equal their first checked form outside comment lines' + ('; ' + ', '.join(bad) if bad else ''))

# 6. controls
bad = []
for c in common.controls():
    try:
        common.apply_control(c)
    except AssertionError as e:
        bad.append(str(e))
report('controls', not bad, f'{len(common.controls()) - len(bad)} controls apply to their mirror' + ('; ' + '; '.join(bad) if bad else ''))

print(f"SOURCE {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
