#!/usr/bin/env python3
"""The coverage arithmetic over the 110 functions, and the generated tables.

usage: coverage.py [<work dir>/results.json] [--write]

Counts the routes of source/manifest.json (Aeneas 22, Verus 96, both 8, union 110, none 0),
maps every control to the mirrored function it changes, and joins the Verus results, so that
each row says what this package re-checks. With a results file, a Verus row is re-checked when
its mirror file verified, at least one control of its function was refuted, and none of its
controls verified. Generates
FUNCTIONS.md (the 110 rows) and TRUSTED.md (every trait interface the mirrors take as a
parameter, verbatim) and compares them with the committed files (--write writes them).
Prints COVERAGE lines; exit 1 on any failure."""
import json
import re
import sys
from collections import Counter
from pathlib import Path

import common

args = [a for a in sys.argv[1:] if not a.startswith('--')]
write = '--write' in sys.argv
M = common.manifest()
rows = M['rows']
ok = True


def report(good, msg):
    global ok
    ok &= good
    print(f"COVERAGE {'ok' if good else 'FAIL'} {msg}", flush=True)


# --- the arithmetic ---------------------------------------------------------------------------
route = Counter(r['route'] for r in rows)
aeneas = route['Aeneas'] + route['both']
verus = route['Verus'] + route['both']
union = sum(r['route'] in ('Aeneas', 'Verus', 'both') for r in rows)
report(len(rows) == 110 and [r['n'] for r in rows] == list(range(1, 111)), f'{len(rows)} relevant functions, numbered 1 to 110')
report((aeneas, verus, route['both'], route['Aeneas'], route['Verus'], union, 110 - union) == (22, 96, 8, 14, 88, 110, 0),
       f"Aeneas {aeneas} (only {route['Aeneas']}), Verus {verus} (only {route['Verus']}), both {route['both']}, "
       f"union {union}, none {110 - union}; {aeneas} + {verus} - {route['both']} = {aeneas + verus - route['both']}")
report(all(bool(r['verus']) == (r['route'] in ('Verus', 'both')) for r in rows), 'every Verus row, and no other, names a mirrored function')
report(sum(r['new_mirror'] for r in rows) == 38 and all(r['verus'] for r in rows if r['new_mirror']),
       f"{sum(r['new_mirror'] for r in rows)} rows use the effect mirrors (rpc, channel, prover_effects, tree)")

# --- controls to rows -------------------------------------------------------------------------
spans = {}
for r in rows:
    if r['verus']:
        text = common.mirror_text(r['verus']['mirror'])
        a, b = common.fn_extent(text, r['verus']['marker'])
        lines = text.splitlines(True)
        spans[r['n']] = (r['verus']['mirror'], len(''.join(lines[:a])), len(''.join(lines[:b])))
by_row = {n: [] for n in spans}
helper = []
for c in common.controls():
    if 'function' in c:  # effect mirrors: the control names its function by its STRENGTH marker
        hit = [r['n'] for r in rows if r['verus'] and r['verus']['marker'] == '// STRENGTH ' + c['function'] + '\n']
    else:
        off = common.control_offset(c)
        hit = [n for n, (m, a, b) in spans.items() if m == c['mirror'] and a <= off < b]
        hit = sorted(hit, key=lambda n: spans[n][2] - spans[n][1])[:1]  # innermost (sum lies in validate_amounts)
    (by_row[hit[0]] if hit else helper).append(c['id'])
none = [n for n in by_row if not by_row[n]]
report(True, f"{sum(map(len, by_row.values()))} controls change a mirrored function, {len(helper)} change a stand-in, "
       f"lemma or example; {len(by_row) - len(none)} of {len(by_row)} Verus rows have a control of their own"
       + (f"; without: {', '.join(str(n) for n in none)}" if none else ''))

# --- results ----------------------------------------------------------------------------------
res = None
if args:
    res = json.loads(Path(args[0]).read_text())
    mirror_ok = {Path(r['label']).name: r['pass'] for r in res['mirrors']}
    control_ok = {r['id']: r['pass'] for r in res['controls']}
    refuted = {r['id'] for r in res['controls'] if r['outcome'] == 'refuted'}
    rlimit = set(res['summary'].get('controls_rlimit', []))


def status(r):
    if not r['verus']:
        return 'frozen: Aeneas, not re-checked here'
    v = r['verus']
    ids = by_row[r['n']]
    if res is None:
        return f"Verus `{v['mirror']}`, {len(ids)} controls"
    nref = sum(i in refuted for i in ids)
    rl = sum(i in rlimit for i in ids)
    good = mirror_ok.get(v['mirror']) and all(control_ok.get(i) for i in ids) and nref >= 1
    s = (f"re-checked: `{v['mirror']}` verifies, {nref} of {len(ids)} controls refuted" if good
         else f"FAIL: `{v['mirror']}` {'verifies' if mirror_ok.get(v['mirror']) else 'does not verify'}, "
              f"{nref} of {len(ids)} controls refuted")
    if rl:
        s += f', {rl} stopped at the solver resource limit'
    if not ids:
        s += ' (no control of its own: see README)'
    if r['route'] == 'both':
        s += '; Aeneas part frozen'
    return s


if res is not None:
    st = [status(r) for r in rows]
    rechecked = sum(s.startswith('re-checked') for s in st)
    report(rechecked == verus, f'{rechecked} of {verus} Verus rows re-checked here, each with a refuted control of its own; {route["Aeneas"]} Aeneas-only rows and the Aeneas half of {route["both"]} rows are frozen')
    lim = [r['n'] for r, s_ in zip(rows, st) if 'resource limit' in s_]
    (Path(args[0]).parent / 'rlimit-rows.json').write_text(json.dumps(lim) + '\n')
    if lim:
        print(f"COVERAGE note rows with a control stopped at the solver resource limit: {', '.join(map(str, lim))}; each has another refuted control", flush=True)
    report(res['summary']['pass'], f"Verus run: {res['summary']['mirrors_pass']} of {res['summary']['mirrors']} mirror files, "
           f"{res['summary']['verified_items']} verified items, {res['summary']['controls']} controls: {res['summary']['controls_refuted']} refuted, "
           f"{len(res['summary']['controls_rlimit'])} stopped at the solver resource limit, {len(res['summary']['controls_failed'])} failed; "
           f"{res['summary']['probes_pass']} of {res['summary']['probes']} probes")

# --- FUNCTIONS.md -----------------------------------------------------------------------------
md = ['# The 110 client functions at a04b8b3', '',
      'Generated by `scripts/coverage.py --write` from `source/manifest.json` and `controls/controls.json`; '
      '`check.sh` regenerates it and requires it unchanged. Line numbers are those of '
      '`pocs/private-payment/shielded-pool/src/lib/` at ethsystems/pocs `a04b8b3`. "Verus" names the '
      'mirror file in `mirrors/` and the number of negative controls that change that function; '
      'RESULT.md gives the run. "Aeneas" rows are taken from the client coverage report of '
      '2026-10-01 (not in this repository) and are not re-checked here.', '',
      f"Aeneas {aeneas}, Verus {verus}, both {route['both']}, Aeneas only {route['Aeneas']}, "
      f"Verus only {route['Verus']}, union {union}, none {110 - union}.", '',
      '| # | Function | File:lines | Route | Verus mirror | Controls | Selected property |', '|---|---|---|---|---|---|---|']
for r in rows:
    v = r['verus']
    md.append(f"| {r['n']} | `{r['function']}` | `{r['file']}:{r['line']}-{r['end']}` | {r['route']} | "
              f"{'`' + v['mirror'] + '`' if v else '-'} | {len(by_row[r['n']]) if v else '-'} | "
              f"{r['property'].replace('|', ';')}{'' if v else ' (frozen)'} |")
md = '\n'.join(md) + '\n'

# --- TRUSTED.md -------------------------------------------------------------------------------
TRAIT = re.compile(r'^pub trait (\w+)', re.M)
tr = ['# Trait interfaces the mirrors take as parameters', '',
      'Generated by `scripts/coverage.py --write`; each block is copied verbatim from the mirror. '
      'A `spec fn` is an abstract function with no body: the proofs assume nothing about its value. '
      'An executable method states its result through its `ensures` clause, and the proofs take that '
      'clause as given: these clauses are the trusted contracts. No implementation of any trait is '
      'given or checked here; that the real library (alloy, ruint, arkworks, light-poseidon, k256, '
      'sealring, serde, toml, tokio, lean-imt, the file system and the prover processes) meets its '
      'contract is assumed.', '',
      '| Mirror | Trait | Spec functions | Executable methods |', '|---|---|---|---|']
blocks, eight = [], []
for p in sorted((common.PKG / 'mirrors').glob('*.rs')):
    text = p.read_text()
    for m in TRAIT.finditer(text):
        i = text.index('{', m.start())
        depth, j = 1, i + 1
        while depth:
            depth += {'{': 1, '}': -1}.get(text[j], 0)
            j += 1
        body = text[m.start():j]
        spec = len(re.findall(r'^\s*(?:open |closed )?spec fn\s', body, re.M))
        execs = len(re.findall(r'^\s*(?:async )?fn\s', body, re.M))
        tr.append(f'| `{p.name}` | `{m.group(1)}` | {spec} | {execs} |')
        blocks += [f'## `{p.name}`: `{m.group(1)}`', '', '```rust', body, '```', '']
        if p.name in ('rpc.rs', 'channel.rs', 'prover_effects.rs', 'tree.rs'):
            eight.append((spec, execs))
tr = '\n'.join(tr + [''] + blocks)
report(len(eight) == 8 and sum(s for s, _ in eight) == 29 and sum(e for _, e in eight) == 31,
       f'{len(eight)} effect interfaces in the effect mirrors, {sum(s for s, _ in eight)} spec functions, '
       f'{sum(e for _, e in eight)} executable contracts; {tr.count("## ")} interfaces in all mirrors')

for name, text in (('FUNCTIONS.md', md), ('TRUSTED.md', tr)):
    path = common.PKG / name
    if write:
        path.write_text(text)
    else:
        report(path.exists() and path.read_text() == text, f'{name} equals its regeneration')
print(f"COVERAGE {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
