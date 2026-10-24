#!/usr/bin/env python3
"""Apply scripts/rename-map.txt to Lean sources, forwards or backwards.

  rename.py forward SRC_DIR DST_DIR   rename every SRC_DIR/**/*.lean (module name = path) into
                                      DST_DIR, at the path of its new module name
  rename.py inverse FILE              print FILE with the map applied backwards

"module" entries apply to the module of an `import` line, and nowhere else. "namespace" and
"name" entries apply to every other line as a whole name component: the name must not touch
an identifier character (a letter, a digit, `_` or `'`) on either side, and may follow a `.`
(`LeanShieldedPool.Game2.Rejection`, `open Game5.Transport`).
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
IMPORT = re.compile(r'^(import\s+)(\S+)(\s*)$')


def load(path=HERE / 'rename-map.txt'):
    mods, names = {}, {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        kind, old, arrow, new = line.split()
        assert arrow == '->' and kind in ('module', 'namespace', 'name'), line
        table = mods if kind == 'module' else names
        assert old not in table, line
        table[old] = new
    for table in (mods, names):
        assert len(set(table.values())) == len(table), 'map is not one-to-one'
    return mods, names


def _fn(mods, names):
    alts = '|'.join(re.escape(a) for a in sorted(names, key=len, reverse=True))
    rx = re.compile(rf"(?<![\w'])(?:{alts})(?![\w'])")

    def apply(text):
        out = []
        for line in text.split('\n'):
            m = IMPORT.match(line)
            if m:
                out.append(m.group(1) + mods.get(m.group(2), m.group(2)) + m.group(3))
            else:
                out.append(rx.sub(lambda x: names[x.group(0)], line))
        return '\n'.join(out)
    return apply


def forward_fn():
    mods, names = load()
    return _fn(mods, names)


def inverse_fn():
    mods, names = load()
    return _fn({v: k for k, v in mods.items()}, {v: k for k, v in names.items()})


def forward_module(module):
    return load()[0].get(module, module)


def module_path(module):
    return Path(*module.split('.')).with_suffix('.lean')


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'forward':
        src, dst = Path(sys.argv[2]), Path(sys.argv[3])
        fwd = forward_fn()
        for f in sorted(src.rglob('*.lean')):
            module = '.'.join(f.relative_to(src).with_suffix('').parts)
            new = module_path(forward_module(module))
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
