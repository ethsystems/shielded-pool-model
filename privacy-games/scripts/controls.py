#!/usr/bin/env python3
"""Run the controls: planted failures that the package checks must reject.

  controls.py [--jobs N]   run every control and compare with controls/EXPECTED.tsv
  controls.py --record     run them and write controls/EXPECTED.tsv (after a reviewed change)

Twenty planted failures and eight copies that must pass. Eighteen adapt the planted cases of
the earlier replay of these games (eight altered sources, eight removed headline audits, two
altered dependency trees); two more cover the pins of this package.

- lean (8): a game module cut after a headline theorem, with one change to the theorem's
  statement and none to its proof (scripts/gen-controls.py). It must fail to compile, at the
  theorem, and not by a parse error or an unknown name. Its `same_` copy (8) must compile.
- census (8): a copy of statements/ with one headline theorem removed or changed; the census
  (scripts/census.py --from build/census.jsonl, so it needs a census run first) must fail.
- pins (4): a tracked change and an untracked file in the fetched VCV-io checkout (each undone
  at once), a lake-manifest.json copy that resolves VCV-io to another revision, and a copy of
  the model files with one byte added; scripts/pins.py must fail.

Each failure must be the first one that controls/EXPECTED.tsv names (one line per control:
name, kind, the first error).
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
CONTROLS = PKG / 'controls'
EXPECTED = CONTROLS / 'EXPECTED.tsv'
LOGS = PKG / 'build' / 'controls'
sys.path.insert(0, str(Path(__file__).resolve().parent))
gen = __import__('gen-controls')

P = 'LeanShieldedPool.'
# name, statements file, theorem, action ('drop' the line, 'edit' its text)
CENSUS = [
    ('census_drop_chosen_world_counterexample', 'INVENTORY.md',
     P + 'ChosenWorldGame.Counterexample.concrete_counterexample', 'drop'),
    ('census_drop_withdraw_transport_bound', 'INVENTORY.md', P + 'WithdrawGame.Transport.advantage_le', 'drop'),
    ('census_drop_sender_bound', 'INVENTORY.md', P + 'SenderGame.advantage_le', 'drop'),
    ('census_drop_sender_rom_bound', 'INVENTORY.md', P + 'SenderGame.ROM.advantage_le_queryBound', 'drop'),
    ('census_edit_sender_rom_commit_bound', 'INVENTORY.md',
     P + 'SenderGame.ROMCommit.advantage_le_queryBound', 'edit'),
    ('census_edit_recipient_rom_collisions', 'INVENTORY.md',
     P + 'RecipientGame.ROMCommit.advantage_le_rom_collisions', 'edit'),
    ('census_edit_raw_chain_commit_only_bound', 'RAW.sha256',
     P + 'ChainGame.CommitOnly.advantage_le_queryBound', 'edit'),
    ('census_drop_raw_chain_rom_collisions', 'RAW.sha256',
     P + 'ChainGame.CommitOnly.advantage_le_rom_collisions', 'drop'),
]
PINS = ['pins_vendor_tracked_change', 'pins_vendor_untracked_file', 'pins_manifest_vcvio_rev',
        'pins_model_file_changed']
BAD_KINDS = ('unknown identifier', 'unknown constant', 'unknown namespace', 'unexpected token',
             'unknown module', 'expected')


def lean(name):
    f = CONTROLS / f'{name}.lean'
    p = subprocess.run(['lake', 'env', 'lean', str(f.relative_to(PKG))], cwd=PKG,
                       capture_output=True, text=True)
    out = p.stdout + p.stderr
    (LOGS / f'{name}.log').write_text(out)
    errors = re.findall(r'^\S+?:(\d+):(\d+): error: (.*)$', out, re.M)
    return p.returncode, errors, out


def run_lean(name):
    code, errors, out = lean(name)
    if name.startswith('same_'):
        if code != 0 or errors or re.search(r': warning:', out):
            return name, 'lean-pass', f'did not compile cleanly: {out.strip()[:200]}', False
        return name, 'lean-pass', 'compiles', True
    if code == 0 or not errors:
        return name, 'lean-fail', 'compiled', False
    line, col, msg = errors[0]
    text = (CONTROLS / f'{name}.lean').read_text().split('\n')
    start = max(i for i, l in enumerate(text, 1) if l.startswith('theorem '))
    ok = int(line) >= start and not msg.startswith(BAD_KINDS)
    return name, 'lean-fail', f'{line}:{col}: {msg}', ok


def run_census(case):
    name, fname, thm, action = case
    with tempfile.TemporaryDirectory() as t:
        d = Path(t)
        for f in ('INVENTORY.md', 'RAW.sha256'):
            shutil.copy(PKG / 'statements' / f, d / f)
        path = d / fname
        lines = path.read_text().split('\n')
        key = (lambda l: l.split(' :: ', 1)[0]) if fname == 'INVENTORY.md' else (lambda l: l.split('  ', 1)[-1])
        idx = [i for i, l in enumerate(lines) if l and not l.startswith('#') and key(l) == thm]
        assert len(idx) == 1, (name, thm)
        i = idx[0]
        if action == 'drop':
            del lines[i]
        elif fname == 'INVENTORY.md':
            lines[i] = lines[i].replace(' / 2', ' / 4', 1) if ' / 2' in lines[i] else lines[i] + ' '
        else:
            lines[i] = ('0' if lines[i][0] != '0' else '1') + lines[i][1:]
        path.write_text('\n'.join(lines))
        p = subprocess.run([sys.executable, str(PKG / 'scripts' / 'census.py'), '--from',
                            str(PKG / 'build' / 'census.jsonl'), '--statements', str(d)],
                           capture_output=True, text=True)
    out = p.stdout + p.stderr
    (LOGS / f'{name}.log').write_text(out)
    first = next((l for l in out.splitlines() if l.startswith('CENSUS ')), 'no CENSUS line')
    return name, 'census', first, p.returncode != 0


def pins(*args):
    p = subprocess.run([sys.executable, str(PKG / 'scripts' / 'pins.py'), *args],
                       capture_output=True, text=True)
    out = p.stdout + p.stderr
    first = next((l for l in out.splitlines() if l.startswith('PINS FAIL')), 'no PINS FAIL line')
    return p.returncode, first, out


def run_pins(name):
    vc = PKG / '.lake' / 'packages' / 'VCVio'
    if name == 'pins_vendor_tracked_change':
        f = vc / 'lean-toolchain'
        data = f.read_bytes()
        try:
            f.write_bytes(data + b'\n')
            code, first, out = pins()
        finally:
            f.write_bytes(data)
    elif name == 'pins_vendor_untracked_file':
        f = vc / 'control-untracked.txt'
        try:
            f.write_text('planted by scripts/controls.py\n')
            code, first, out = pins()
        finally:
            f.unlink(missing_ok=True)
    elif name == 'pins_manifest_vcvio_rev':
        with tempfile.TemporaryDirectory() as t:
            m = json.loads((PKG / 'lake-manifest.json').read_text())
            for p in m['packages']:
                if p['name'] == 'VCVio':
                    p['rev'] = 'f3df0ac18aa5ae72b3e920ad5460492aa039b4f7'
            (Path(t) / 'lake-manifest.json').write_text(json.dumps(m))
            code, first, out = pins('--manifest', str(Path(t) / 'lake-manifest.json'))
    else:
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'pkg'
            pool = Path(t) / 'LeanShieldedPool' / 'Pool'
            pool.mkdir(parents=True)
            root.mkdir()
            for f in ('State.lean', 'Tx.lean', 'Events.lean'):
                shutil.copy(PKG.parent / 'LeanShieldedPool' / 'Pool' / f, pool / f)
            with open(pool / 'State.lean', 'ab') as fh:
                fh.write(b'\n')
            code, first, out = pins('--model-root', str(root))
    (LOGS / f'{name}.log').write_text(out)
    return name, 'pins', first, code != 0


def main():
    args = sys.argv[1:]
    record = '--record' in args
    jobs = int(args[args.index('--jobs') + 1]) if '--jobs' in args else 1
    LOGS.mkdir(parents=True, exist_ok=True)
    names = [c[0] for c in gen.CASES]
    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(run_lean, names + [f'same_{n}' for n in names]))
    results += [run_census(c) for c in CENSUS]
    results += [run_pins(n) for n in PINS]
    if record:
        EXPECTED.write_text('# name\tkind\tfirst error (or "compiles"); written by scripts/controls.py --record\n'
                            + ''.join(f'{n}\t{k}\t{m}\n' for n, k, m, _ in results))
    want = {}
    for l in EXPECTED.read_text().splitlines():
        if l and not l.startswith('#'):
            n, k, m = l.split('\t', 2)
            want[n] = (k, m)
    bad = 0
    for n, k, m, ok in results:
        good = ok and want.get(n) == (k, m)
        bad += not good
        print(f"CONTROL {'ok  ' if good else 'BAD '} {k:9} {n}: {m}")
    extra = sorted(want.keys() - {r[0] for r in results})
    for n in extra:
        bad += 1
        print(f'CONTROL BAD  listed in EXPECTED.tsv but not run: {n}')
    fails = sum(1 for r in results if r[1] != 'lean-pass')
    if bad:
        print(f'CONTROLS FAIL: {bad} of {len(results)} controls')
        sys.exit(1)
    print(f'CONTROLS PASS: {fails} planted failures rejected as expected, '
          f'{len(results) - fails} unchanged copies compile')


if __name__ == '__main__':
    main()
