#!/usr/bin/env python3
"""Regenerate the controls, compare them with controls/, and compile each one.

  controls.py [--jobs N]           check every control against controls/EXPECTED.tsv
  controls.py [--jobs N] --write   write controls/EXPECTED.tsv from this run (after review)

A `fail` control must fail to compile, with the first error of EXPECTED.tsv, and that error
must not be a parse error or an unknown name (that would be a broken control, not a refuted
statement). A `pass` control must compile, and its `#print axioms` line must list only
`propext`, `Classical.choice` and `Quot.sound`. Logs go to build/controls/.
"""
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
CTL = PKG / 'controls'
EXP = CTL / 'EXPECTED.tsv'
LOGS = PKG / 'build' / 'controls'
FLAGS = ['-M8192', '--tstack=65536', '-DElab.async=false', '-DmaxRecDepth=10000',
         '-DmaxHeartbeats=4000000']
BROKEN = re.compile(r'unexpected token|unknown identifier|unknown constant|unknown namespace')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def first_error(text):
    for line in text.splitlines():
        m = re.match(r'^controls/[^:]+\.lean:(\d+):(\d+): error: (.*)$', line)
        if m:
            return f'{m.group(1)}:{m.group(2)}: {m.group(3)[:160]}'
    return ''


def run(name):
    p = subprocess.run(['lake', 'env', 'lean', *FLAGS, f'controls/{name}.lean'], cwd=PKG,
                       capture_output=True, text=True, env=None)
    out = p.stdout + p.stderr
    (LOGS / f'{name}.log').write_text(out)
    return name, p.returncode, out


def main():
    args = sys.argv[1:]
    jobs = 1
    if args[:1] == ['--jobs']:
        jobs, args = int(args[1]), args[2:]
    write = args == ['--write']
    bad = []
    with tempfile.TemporaryDirectory() as t:
        listing = subprocess.run([sys.executable, str(PKG / 'scripts' / 'gen-controls.py'), t],
                                 capture_output=True, text=True, check=True).stdout
        verdicts = dict(l.split() for l in listing.splitlines())
        for name in verdicts:
            if (Path(t) / f'{name}.lean').read_bytes() != (CTL / f'{name}.lean').read_bytes():
                bad.append(f'{name}: controls/{name}.lean differs from the generator output')
        extra = {f.stem for f in CTL.glob('*.lean')} - set(verdicts)
        for name in sorted(extra):
            bad.append(f'{name}: controls/{name}.lean is not a generated control')
    LOGS.mkdir(parents=True, exist_ok=True)
    expected = {}
    if not write:
        for l in EXP.read_text().splitlines():
            if l and not l.startswith('#'):
                n, v, e = (l.split('\t') + [''])[:3]
                expected[n] = (v, e)
        for n in sorted(set(expected) ^ set(verdicts)):
            bad.append(f'{n}: in only one of EXPECTED.tsv and the generator')
    rows = []
    with ThreadPoolExecutor(jobs) as ex:
        for name, ec, out in ex.map(run, list(verdicts)):
            v = verdicts[name]
            err = first_error(out)
            if v == 'pass':
                if ec != 0:
                    bad.append(f'{name}: must compile, failed: {err}')
                for m in re.finditer(r"'[^']+' depends on axioms: \[([^\]]*)\]", out):
                    axs = {a.strip() for a in m.group(1).split(',') if a.strip()}
                    if axs - ALLOWED:
                        bad.append(f'{name}: axioms {sorted(axs)}')
                if 'axioms' not in out:
                    bad.append(f'{name}: no #print axioms output')
                err = ''
            else:
                if ec == 0:
                    bad.append(f'{name}: must fail, compiled')
                elif BROKEN.search(err):
                    bad.append(f'{name}: broken control (parse or name error): {err}')
                elif not write and expected.get(name, ('', ''))[1] != err:
                    bad.append(f'{name}: first error changed: {err}')
            rows.append((name, v, err))
            print(f'{v} exit={ec} {name} {err}', flush=True)
    if write:
        EXP.write_text('# control\tverdict\tfirst error (line:col: message), for fail controls\n'
                       + ''.join(f'{n}\t{v}\t{e}\n' for n, v, e in rows))
    if bad:
        for b in bad:
            print('CONTROL', b)
        print(f'CONTROLS FAIL: {len(bad)} problems in {len(rows)} controls')
        sys.exit(1)
    npass = sum(1 for r in rows if r[1] == 'pass')
    print(f'CONTROLS PASS: {len(rows) - npass} must-fail controls fail, {npass} must-pass copies compile')


if __name__ == '__main__':
    main()
