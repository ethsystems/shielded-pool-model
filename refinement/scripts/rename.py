#!/usr/bin/env python3
"""Apply scripts/rename-map.txt to Lean sources, forwards or backwards.

  rename.py forward SRC_DIR DST_DIR   rename every SRC_DIR/**/*.lean into DST_DIR, moving each
                                      file to the path of its new module name
  rename.py inverse FILE              print FILE with the map applied backwards

"module" entries rename the module names of `import` lines (whole names). "namespace" entries
are a whole-identifier substitution, longest name first: an identifier character is a letter, a
digit, `_` or `'`, and a name does not match right after a `.`, so only the first components of
a qualified name are renamed (the full dotted forms have their own entries). "control" entries
only document the earlier names of the controls, and "label" entries the working labels of
reports and of the claim board (BOARD.md at the repository root); neither is applied.
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
        kind, old, arrow, new = line.split(None, 3)
        assert arrow == '->' and kind in ('module', 'namespace', 'control', 'label'), line
        if kind in ('module', 'namespace'):
            assert ' ' not in new, line
            rows.append((kind, old, new))
    for kind in ('module', 'namespace'):
        olds = [r[1] for r in rows if r[0] == kind]
        news = [r[2] for r in rows if r[0] == kind]
        assert len(set(olds)) == len(olds) and len(set(news)) == len(news), 'map is not one-to-one'
        assert not set(olds) & set(news), 'a name is both an old and a new name'
    return rows


def _compile(rows, backwards):
    mods = {(n if backwards else o): (o if backwards else n) for k, o, n in rows if k == 'module'}
    nss = {(n if backwards else o): (o if backwards else n) for k, o, n in rows if k == 'namespace'}
    alts = '|'.join(re.escape(a) + f"(?![{IDENT}])" for a in sorted(nss, key=len, reverse=True))
    rx = re.compile(f"(?<![{IDENT}.])(?:{alts})")
    imp = re.compile(r'^(import\s+)(\S+)', re.M)

    def apply(text):
        text = imp.sub(lambda m: m.group(1) + mods.get(m.group(2), m.group(2)), text)
        return rx.sub(lambda m: nss[m.group(0)], text)

    return apply, mods


def forward_fn(rows=None):
    return _compile(rows or load(), False)


def inverse_fn(rows=None):
    return _compile(rows or load(), True)


def module_path(module):
    return Path(*module.split('.')).with_suffix('.lean')


def main():
    cmd = sys.argv[1]
    if cmd == 'forward':
        src, dst = Path(sys.argv[2]), Path(sys.argv[3])
        fwd, mods = forward_fn()
        for f in sorted(src.rglob('*.lean')):
            module = '.'.join(f.relative_to(src).with_suffix('').parts)
            new = module_path(mods.get(module, module))
            out = dst / new
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(fwd(f.read_text()))
            print(f'{f.relative_to(src)} -> {new}')
    elif cmd == 'inverse':
        sys.stdout.write(inverse_fn()[0](Path(sys.argv[2]).read_text()))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
