#!/usr/bin/env python3
"""Check (or write) PINS.sha256, and check the dependency checkouts.

  pins.py                check every pinned file; that the pinned model files are exactly the
                         import closure of this package's modules in ../LeanShieldedPool; that
                         the pinned circuits-lampe files are exactly the closure the fold bridge
                         imports, with the fixed files below; that each lakefile require matches
                         its manifest entry; and that the toolchains agree
  pins.py --deps main    after a fetch: each git package of the parent's and this package's
                         manifests is checked out in ../.lake/packages at its manifest rev, from
                         its manifest URL, with no change and no untracked file
  pins.py --deps fold-bridge
                         the same for the manifest of ../circuits-lampe and its .lake/packages
  pins.py --write        write PINS.sha256 from the current files (after a reviewed change)

Pinned: the model modules of the parent directory that the package imports, directly or through
each other (the refinement is a statement about these files); the parent's lakefile.toml,
lake-manifest.json and lean-toolchain; this package's toolchain and manifest; and, for the fold
bridge, every source file of ../circuits-lampe that the bridge imports, directly or through each
other (proof modules and extracted circuits), every source and the lakefile of each extracted
package (the bridge build runs `lake build` of all of them), that package's lakefile, manifest
and toolchain, and the circuits-lampe scripts this package runs or reads (scripts/build.py,
scripts/rename.py, scripts/rename-map.txt).
"""
import hashlib
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ROOT = PKG.parent
CL = ROOT / 'circuits-lampe'
FB = PKG / 'fold-bridge'
PINS = PKG / 'PINS.sha256'
GROUPS = ['Refinement', 'Tree', 'Balance', 'Journey', 'Gas', 'fold-bridge/FoldBridge']
FIXED = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
         'refinement/lean-toolchain', 'refinement/lake-manifest.json']
CL_FIXED = ['circuits-lampe/lakefile.toml', 'circuits-lampe/lake-manifest.json',
            'circuits-lampe/lean-toolchain', 'circuits-lampe/scripts/build.py',
            'circuits-lampe/scripts/rename.py', 'circuits-lampe/scripts/rename-map.txt']
TOOLCHAINS = ['lean-toolchain', 'refinement/lean-toolchain', 'circuits-lampe/lean-toolchain']
IMPORT = re.compile(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)', re.M)


def imports(f):
    return IMPORT.findall(f.read_text())


def model_closure():
    todo = [i for g in GROUPS for f in (PKG / g).rglob('*.lean') for i in imports(f)
            if i.startswith('LeanShieldedPool.')]
    seen = set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        f = ROOT / Path(*m.split('.')).with_suffix('.lean')
        todo += [i for i in imports(f) if i.startswith('LeanShieldedPool.')]
    return sorted(str(Path(*m.split('.')).with_suffix('.lean')) for m in seen)


def manifest(d):
    return json.loads((d / 'lake-manifest.json').read_text())


def cl_path_packages():
    return [(CL / p['dir']).resolve() for p in manifest(CL)['packages'] if p['type'] == 'path']


def bridge_closure():
    """(the circuits-lampe source files the fold bridge imports, problems)."""
    ours = [FB, PKG]
    theirs = [CL] + cl_path_packages()
    bad, files, seen = [], set(), set()
    todo = [i for f in FB.rglob('*.lean') for i in imports(f)]

    def find(m, bases):
        rel = Path(*[c.strip('«»') for c in re.findall(r'«[^»]*»|[^.]+', m)]).with_suffix('.lean')
        return [b / rel for b in bases if (b / rel).is_file()]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        mine = find(m, ours + ([ROOT] if m.startswith('LeanShieldedPool.') else []))
        cl = find(m, theirs)
        if len(mine) + len(cl) > 1:
            bad.append(f'module {m} has more than one source: {[str(p.relative_to(ROOT)) for p in mine + cl]}')
        for f in mine + cl:
            todo += imports(f)
        files.update(str(f.relative_to(ROOT)) for f in cl)
    return sorted(files), bad


def cl_files():
    """The pinned circuits-lampe set: the bridge's import closure, and every source and the
    lakefile of each extracted package (the bridge build runs `lake build` of all of them)."""
    closure, bad = bridge_closure()
    extracted = [str(f.relative_to(ROOT)) for d in cl_path_packages()
                 for f in [d / 'lakefile.toml', *d.rglob('*.lean')] if '.lake' not in f.parts]
    return sorted(set(closure + extracted + CL_FIXED)), bad


def requires(d):
    """Each [[require]] of d/lakefile.toml against its entry in d/lake-manifest.json."""
    bad = []
    pk = {p['name'].strip('«»'): p for p in manifest(d)['packages']}
    for r in tomllib.loads((d / 'lakefile.toml').read_text()).get('require', []):
        name, p = r['name'].strip('«»'), pk.get(r['name'].strip('«»'))
        where = f'{d.relative_to(ROOT) if d != ROOT else "."}: require {name}'
        if p is None:
            bad.append(f'{where} is not in lake-manifest.json')
        elif 'git' in r:
            rev = r.get('rev')
            ok = (p['type'] == 'git' and p['url'] == r['git'] and p.get('subDir') == r.get('subDir')
                  and (p['rev'] == rev if re.fullmatch(r'[0-9a-f]{40}', rev or '') else p['inputRev'] == rev))
            if not ok:
                bad.append(f'{where}: lakefile and manifest disagree on the URL, rev or subDir')
        elif 'path' in r:
            if p['type'] != 'path' or (d / p['dir']).resolve() != (d / r['path']).resolve():
                bad.append(f'{where}: lakefile and manifest disagree on the path')
        else:
            bad.append(f'{where}: neither git nor path')
    return bad


def same_revs():
    """Mathlib and its dependencies at the same commits in the circuits-lampe workspace."""
    parent = {p['name']: p for p in manifest(ROOT)['packages'] if p['type'] == 'git'}
    bad = []
    for p in manifest(CL)['packages']:
        q = parent.get(p['name'])
        if q and (q['url'], q['rev']) != (p['url'], p['rev']):
            bad.append(f'{p["name"]} differs between the parent and the circuits-lampe manifests')
    return bad


def checkouts(d):
    """The git packages of d/lake-manifest.json against their checkouts: (count, problems)."""
    m = manifest(d)
    base = d / m.get('packagesDir', '.lake/packages')
    bad, n = [], 0
    for p in m['packages']:
        if p['type'] != 'git':
            continue
        n += 1
        c = base / p['name'].strip('«»')
        g = lambda *a: subprocess.run(['git', '-C', str(c), *a], capture_output=True, text=True)
        where = f'{p["name"]} ({c.relative_to(ROOT)})'
        if not (c / '.git').exists():
            bad.append(f'{where}: no git checkout')
            continue
        head = g('rev-parse', 'HEAD').stdout.strip()
        if head != p['rev']:
            bad.append(f'{where}: HEAD is {head}, the manifest says {p["rev"]}')
        if g('remote', 'get-url', 'origin').stdout.strip() != p['url']:
            bad.append(f'{where}: origin is not {p["url"]}')
        diff = g('diff', 'HEAD')
        if diff.returncode != 0 or diff.stdout:
            bad.append(f'{where}: differs from its commit (git diff HEAD)')
        st = g('status', '--porcelain', '--untracked-files=all')
        if st.returncode != 0 or st.stdout:
            bad.append(f'{where}: changed or untracked files: {st.stdout.split(chr(10))[:3]}')
    return n, bad


def sha(p):
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()


def check_deps(which):
    dirs = {'main': [ROOT, PKG], 'fold-bridge': [CL]}[which]
    bad, n = [], 0
    for d in dirs:
        k, b = checkouts(d)
        n, bad = n + k, bad + b
    return n, bad


def main():
    args = sys.argv[1:]
    if args[:1] == ['--deps']:
        n, bad = check_deps(args[1])
        for b in bad:
            print('DEPS', b)
        if bad:
            sys.exit(f'DEPS FAIL ({args[1]}): {len(bad)} problems')
        print(f'DEPS PASS ({args[1]}): {n} git packages at their manifest revs, unchanged, '
              f'no untracked files')
        return
    model = model_closure()
    cl, bad = cl_files()
    files = model + FIXED + cl
    if args == ['--write']:
        if bad:
            sys.exit('\n'.join(bad))
        lines = ['# Pins of the refinement package: sha256 of each file outside the package that its',
                 '# results rest on, relative to the repository root. Checked by scripts/pins.py.',
                 '# The LeanShieldedPool/ lines are the model modules the package imports, directly or',
                 '# through each other: the refinement theorems are statements about these files.',
                 '# The circuits-lampe/ lines are the sources the fold bridge imports from that package,',
                 '# directly or through each other, its lakefiles, manifest and toolchain, and the',
                 '# scripts of that package that this one runs or reads.']
        lines += [f'{sha(p)}  {p}' for p in files]
        PINS.write_text('\n'.join(lines) + '\n')
        print(f'wrote {PINS.name}: {len(files)} files ({len(model)} model modules, '
              f'{len(cl)} circuits-lampe files)')
        return
    pinned = {}
    for l in PINS.read_text().splitlines():
        if l and not l.startswith('#'):
            h, p = l.split('  ', 1)
            pinned[p] = h
    pinned_model = sorted(p for p in pinned if p.startswith('LeanShieldedPool/'))
    if pinned_model != model:
        bad.append(f'the pinned model modules are not the import closure: '
                   f'{sorted(set(pinned_model) ^ set(model))}')
    pinned_cl = sorted(p for p in pinned if p.startswith('circuits-lampe/'))
    if pinned_cl != cl:
        bad.append(f'the pinned circuits-lampe files are not the closure the fold bridge imports: '
                   f'{sorted(set(pinned_cl) ^ set(cl))[:10]}')
    for p in sorted(set(files) - set(pinned)):
        bad.append(f'not pinned: {p}')
    for p, h in sorted(pinned.items()):
        if not (ROOT / p).is_file():
            bad.append(f'missing: {p}')
        elif sha(p) != h:
            bad.append(f'differs from its pin: {p}')
    if len({(ROOT / t).read_text() for t in TOOLCHAINS}) != 1:
        bad.append(f'the toolchains differ: {TOOLCHAINS}')
    bad += requires(ROOT) + requires(PKG) + requires(CL) + same_revs()
    if bad:
        for b in bad:
            print('PINS', b)
        sys.exit(f'PINS FAIL: {len(bad)} problems')
    print(f'PINS PASS: {len(pinned)} files ({len(model)} model modules the package imports, '
          f'{len(pinned_cl)} circuits-lampe files the fold bridge rests on); requires match the '
          f'manifests')


if __name__ == '__main__':
    main()
