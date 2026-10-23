#!/usr/bin/env python3
"""Apply scripts/rename-map.txt to Lean sources, forwards or backwards.

  rename.py forward SRC_DIR DST_DIR   rename every SRC_DIR/**/*.lean into DST_DIR, moving each
                                      file to the path of its new module name
  rename.py inverse FILE              print FILE with the map applied backwards

The map is a whole-identifier substitution, longest name first. An identifier character is a
letter, a digit, `_` or `'`; a name also does not match right after a `.`, so only the first
components of a qualified name are renamed. A "prefix" entry renames a Noir path prefix
(`stage5::` and so on) wherever it starts an identifier. "control" entries only document the
names of the controls and are not applied.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
IDENT = r"A-Za-z0-9_'"


def load(path=HERE / 'rename-map.txt'):
    rows = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        kind, old, arrow, new = line.split()
        assert arrow == '->', line
        if kind == 'control':
            continue
        rows.append((kind, old, new))
    olds = [r[1] for r in rows]
    news = [r[2] for r in rows]
    assert len(set(olds)) == len(olds) and len(set(news)) == len(news), 'map is not one-to-one'
    return rows


def _compile(pairs):
    names = [a for a, _, _ in pairs]
    table = {a: b for a, b, _ in pairs}
    alts = []
    for a, _, prefix in sorted(pairs, key=lambda r: -len(r[0])):
        alts.append(re.escape(a) if prefix else re.escape(a) + f"(?![{IDENT}])")
    rx = re.compile(f"(?<![{IDENT}.])(?:" + '|'.join(alts) + ')')
    return lambda text: rx.sub(lambda m: table[m.group(0)], text), names


def forward_fn(rows=None):
    rows = rows or load()
    return _compile([(o, n, k == 'prefix') for k, o, n in rows])[0]


def inverse_fn(rows=None):
    rows = rows or load()
    return _compile([(n, o, k == 'prefix') for k, o, n in rows])[0]


def module_path(module):
    return Path(*module.split('.')).with_suffix('.lean')


def main():
    cmd = sys.argv[1]
    if cmd == 'forward':
        src, dst = Path(sys.argv[2]), Path(sys.argv[3])
        fwd = forward_fn()
        for f in sorted(src.rglob('*.lean')):
            module = '.'.join(f.relative_to(src).with_suffix('').parts)
            new = module_path(fwd(module))
            out = dst / new
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(fwd(f.read_text()))
            print(f'{f.relative_to(src)} -> {new}')
    elif cmd == 'inverse':
        sys.stdout.write(inverse_fn()(Path(sys.argv[2]).read_text()))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
