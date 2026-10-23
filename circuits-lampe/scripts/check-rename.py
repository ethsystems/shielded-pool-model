#!/usr/bin/env python3
"""Check that the proof modules differ from their first form only in names and comments.

scripts/rename-origins.txt has one line per module:
    <sha256 of the original file> <sha256 of its code> <original path> <path here>
"Code" is the file with every comment removed (line comments, nested block comments and
docstrings), trailing spaces removed and blank lines dropped.

  check-rename.py                  apply scripts/rename-map.txt backwards to each file here,
                                   take its code and compare the sha256 with the pin
  check-rename.py --originals DIR  also check DIR/<original path> against both pins and print
                                   the full residual diff (it must touch comments only)
  check-rename.py --record DIR     write rename-origins.txt from the originals in DIR, using
                                   the forward map to find each file here
"""
import difflib
import hashlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
sys.path.insert(0, str(HERE))
import rename  # noqa: E402

ORIGINS = HERE / 'rename-origins.txt'


def strip_comments(text):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text.startswith('/-', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c == '«':
            j = text.find('»', i)
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(c)
            i += 1
    lines = [l.rstrip() for l in ''.join(out).split('\n')]
    return '\n'.join(l for l in lines if l) + '\n'


def sha(s):
    return hashlib.sha256(s.encode() if isinstance(s, str) else s).hexdigest()


def main():
    args = sys.argv[1:]
    if args[:1] == ['--record']:
        src = Path(args[1])
        fwd = rename.forward_fn()
        rows = []
        for f in sorted(src.rglob('*.lean')):
            rel = f.relative_to(src)
            module = '.'.join(rel.with_suffix('').parts)
            new = rename.module_path(fwd(module))
            assert (PKG / new).exists(), new
            rows.append(f'{sha(f.read_bytes())} {sha(strip_comments(f.read_text()))} {rel} {new}')
        ORIGINS.write_text('\n'.join(rows) + '\n')
        print(f'recorded {len(rows)} modules')
        return
    originals = Path(args[1]) if args[:1] == ['--originals'] else None
    inv = rename.inverse_fn()
    bad = changed = 0
    rows = [l.split() for l in ORIGINS.read_text().splitlines() if l]
    for raw, code, old, new in rows:
        text = (PKG / new).read_text()
        back = inv(text)
        if sha(strip_comments(back)) != code:
            bad += 1
            print(f'CODE DIFFERS {new} (from {old})')
        if originals is not None:
            o = originals / old
            if sha(o.read_bytes()) != raw or sha(strip_comments(o.read_text())) != code:
                bad += 1
                print(f'ORIGINAL DIFFERS FROM PIN {old}')
                continue
            d = list(difflib.unified_diff(o.read_text().splitlines(), back.splitlines(),
                                          f'original/{old}', f'renamed-back/{new}', lineterm='', n=0))
            if d:
                changed += 1
                print('\n'.join(d))
    known = {r[3] for r in rows}
    extra = [str(p.relative_to(PKG)) for p in PKG.rglob('*.lean')
             if not p.relative_to(PKG).parts[0] in ('controls', 'extracted', '.lake')
             and str(p.relative_to(PKG)) not in known and p.name != 'Census.lean']
    for e in extra:
        bad += 1
        print(f'NOT IN rename-origins.txt: {e}')
    tail = f', {changed} with comment changes' if originals is not None else ''
    if bad:
        print(f'RENAME CHECK FAIL: {bad} problems in {len(rows)} modules')
        sys.exit(1)
    print(f'RENAME CHECK PASS: {len(rows)} modules, code equal to the originals after the inverse map{tail}')


if __name__ == '__main__':
    main()
