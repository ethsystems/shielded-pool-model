#!/usr/bin/env python3
"""Source scan: forbidden words in Lean files, kernel options in lakefiles.

Every Lean file of this package (modules, census files and controls) is scanned as text; the
model files of the parent directory that the package imports (PINS.sha256) are scanned with their
comments removed, since their prose names the words it excludes. Forbidden: `sorry`, `admit`,
`native_decide`, `implemented_by`, `extern`, `unsafe`, `skipKernelTC`, and a line that starts a
declaration with `axiom` or `opaque`. Lakefiles (this package's, the parent's and the pinned
circuits-lampe ones the fold bridge builds with): `skipKernelTC` and `debug.` options.
"""
import importlib.util
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
ROOT = PKG.parent
spec = importlib.util.spec_from_file_location('cr', HERE / 'check-rename.py')
cr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cr)

WORDS = re.compile(r'\b(sorry|admit|native_decide|implemented_by|extern|unsafe|skipKernelTC)\b'
                   r'|^\s*((private|protected|noncomputable|partial)\s+)*(axiom|opaque)\s', re.M)


def main():
    own = [p for p in PKG.rglob('*.lean') if not {'.lake', 'build'} & set(p.relative_to(PKG).parts)]
    pinned = [ROOT / l.split('  ', 1)[1] for l in (PKG / 'PINS.sha256').read_text().splitlines()
              if l and not l.startswith('#')]
    model = [p for p in pinned if p.relative_to(ROOT).parts[0] == 'LeanShieldedPool']
    lakefiles = [PKG / 'lakefile.toml', ROOT / 'lakefile.toml'] + \
        [p for p in pinned if p.relative_to(ROOT).parts[0] == 'circuits-lampe' and p.name == 'lakefile.toml']
    hits = []
    for p in own:
        for m in WORDS.finditer(p.read_text()):
            hits.append(f'{p.relative_to(PKG)}: {m.group(0).strip()}')
    for p in model:
        for m in WORDS.finditer(cr.strip_comments(p.read_text())):
            hits.append(f'{p.relative_to(ROOT)} (code): {m.group(0).strip()}')
    for lf in lakefiles:
        if re.search(r'skipKernelTC|debug\.', lf.read_text()):
            hits.append(f'{lf.relative_to(ROOT)}: kernel option')
    if hits:
        print('\n'.join(hits[:20]))
        sys.exit(f'SCAN FAIL: {len(hits)} hits')
    print(f'SCAN PASS: {len(own)} Lean files of the package (text) and {len(model)} model files '
          f'(code): no sorry, admit, native_decide, axiom, opaque, extern, implemented_by, unsafe '
          f'or skipKernelTC; {len(lakefiles)} lakefiles: no kernel option')


if __name__ == '__main__':
    main()
