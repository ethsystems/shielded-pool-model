#!/usr/bin/env python3
"""Replay check for the hash-agreement package (driven by ../check.sh).

usage: replay.py check     run every stage; exit 0 only if build/observed.json equals expected.json

Stages: tool pins, source inventory, input hashes, the upstream sources at their pins
(scripts/sources.py), regeneration of the Lean files from the inputs (byte-for-byte against the
committed ones), the Python vector replay, the forbidden-token scan, Mathlib dependencies, a
fresh sequential build of the five modules (timed, with peak RSS), the theorem census
(statement and axioms of every declared theorem; standard axioms only, auxiliary lemmas
included), the negative control (must fail at the two recorded kernel checks), the Lean vector
test, and an exact comparison with expected.json. Missing,
duplicate and unexpected entries fail.
"""
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

PKG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(PKG, 'build')
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
# The standard-axiom allowlist. It lives here, not in expected.json, so that a re-blessed
# expected.json cannot widen it.
ALLOWED_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
FORBIDDEN = re.compile(r'\b(sorry|admit|native_decide|axiom|extern|implemented_by|unsafe|opaque|'
                       r'skipKernelTC)\b')
# The scan reads every Lean file of the package and the Lake configuration (which could pass
# options to every module).
SCANNED = re.compile(r'(\.lean|^lakefile\.toml)$')
MODULES = ['Base', 'Sol', 'RoundsD', 'Controls', 'Full']
GENERATED = ['HashAgreement/Base.lean', 'HashAgreement/Sol.lean', 'HashAgreement/Full.lean',
             'HashAgreement/RoundsD.lean', 'HashAgreement/Controls.lean', 'Neg/RoundsNeg.lean',
             'test/Vectors.lean', 'blocks.sha256']
GENERATORS = ['scripts/common.py', 'scripts/gen_sol.py', 'scripts/gen_lean.py']
# The claims the README states. Each must be in expected.json and in the census.
HEADLINE = ['HashAgreement.noirPermute_eq_plainPerm', 'HashAgreement.noirHash2_eq_plainHash2',
            'HashAgreement.solHashSeg_eq_plainHash2', 'HashAgreement.solHashSeg_eq_noirHash2',
            'HashAgreement.round4_wrong_false']
# Auxiliary theorem names (kernel-check proofs, equation and structure lemmas): their axioms
# are checked, their statements are not pinned.
AUX = re.compile(r'^(_.*|eq_\d+|eq_def|injEq|inj|sizeOf_spec)$')
SECTIONS = ['toolchain', 'source_files', 'inputs', 'generated_files', 'python_vectors',
            'theorems', 'negative_control', 'lean_vectors']
UNPINNED = {'README.md', 'expected.json', '.gitignore'}
MATHLIB_REV_RE = re.compile(r'"name":\s*"mathlib"')


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def log(msg):
    print(f'[{time.strftime("%H:%M:%S")}] {msg}', flush=True)


class Fatal(Exception):
    pass


def run(cmd, check=True, env=None, cwd=PKG):
    """Run a command; return (rc, text, wall_s, maxrss_kb of its largest terminated descendant)."""
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = p.stdout.read().decode(errors='replace')
    _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    wall = time.monotonic() - t0
    if check and rc != 0:
        raise Fatal(f'command failed (rc {rc}): {" ".join(cmd)}\n{text[-2000:]}')
    return rc, text, wall, ru.ru_maxrss


def load_json_strict(path):
    def no_dups(pairs):
        keys = [k for k, _ in pairs]
        dups = sorted({k for k in keys if keys.count(k) > 1})
        if dups:
            raise Fatal(f'DUPLICATE keys in {os.path.basename(path)}: {dups}')
        return dict(pairs)
    with open(path) as f:
        return json.load(f, object_pairs_hook=no_dups)


def walk_files():
    out = []
    for root, dirs, files in os.walk(PKG):
        rel_root = os.path.relpath(root, PKG)
        dirs[:] = [d for d in dirs if d != '__pycache__' and not d.startswith('.') and not (rel_root == '.' and d == 'build')]
        for f in files:
            if not f.startswith('.'):
                out.append(os.path.normpath(os.path.join(rel_root, f)))
    return sorted(out)


# ---------------------------------------------------------------- stages

def stage_tools(obs):
    with open(os.path.join(PKG, 'lean-toolchain')) as f:
        tc = f.read().strip()
    _, ver, _, _ = run(['lake', '--version'])
    obs['toolchain'] = {'lean-toolchain': tc, 'lake_reports_lean_4_33_1': 'Lean version 4.33.1' in ver,
                        'python_ge_3_10': sys.version_info >= (3, 10)}
    log(f'tools: {tc}; {ver.strip()}; python {sys.version.split()[0]}')


def stage_inventory(obs):
    src = {}
    for rel in walk_files():
        if rel in UNPINNED or rel in GENERATED or (rel.startswith('inputs/') and not rel.endswith('.md')):
            continue
        src[rel] = sha(os.path.join(PKG, rel))
    obs['source_files'] = src
    log(f'inventory: {len(src)} pinned source files')


def stage_inputs(obs):
    inp = {rel: sha(os.path.join(PKG, rel)) for rel in walk_files()
           if rel.startswith('inputs/') and not rel.endswith('.md')}
    obs['inputs'] = inp
    log(f'inputs: {len(inp)} files hashed')


def stage_sources():
    rc, text, _, _ = run(['python3', 'scripts/sources.py'], check=False)
    if rc != 0:
        raise Fatal(f'SOURCES FAILED (rc {rc}):\n{text[-2000:]}')
    for line in text.strip().split('\n'):
        log(line)


def stage_regen(obs):
    tmp = tempfile.mkdtemp(prefix='regen.', dir=BUILD)
    try:
        run(['python3', 'scripts/gen_lean.py', '--out', tmp])
        bad = []
        for rel in GENERATED:
            a, b = os.path.join(PKG, rel), os.path.join(tmp, rel)
            if not os.path.exists(a):
                bad.append(f'{rel}: committed file missing')
            elif not os.path.exists(b):
                bad.append(f'{rel}: generator did not write it')
            elif open(a, 'rb').read() != open(b, 'rb').read():
                bad.append(f'{rel}: committed file differs from the regenerated one')
        if bad:
            raise Fatal('REGENERATION MISMATCH\n' + '\n'.join(bad))
    finally:
        shutil.rmtree(tmp)
    obs['generated_files'] = {rel: sha(os.path.join(PKG, rel)) for rel in GENERATED}
    log(f'regen: {len(GENERATED)} generated files match the generator output byte for byte')


def stage_python_vectors(obs):
    rc, text, wall, _ = run(['python3', 'scripts/check_vectors.py'], check=False)
    last = [l for l in text.strip().split('\n') if l.startswith('{')]
    if rc != 0 or not last:
        raise Fatal(f'PYTHON VECTOR REPLAY FAILED (rc {rc}):\n{text[-2000:]}')
    obs['python_vectors'] = json.loads(last[-1])
    log(f'python vectors: {obs["python_vectors"]} ({wall:.0f} s)')


def stage_scan(failures):
    n = 0
    for rel in walk_files():
        if not SCANNED.search(rel):
            continue
        n += 1
        for k, line in enumerate(open(os.path.join(PKG, rel), encoding='utf-8'), 1):
            m = FORBIDDEN.search(line)
            if m:
                failures.append(f'FORBIDDEN TOKEN {m.group(1)!r} at {rel}:{k}')
    log(f'scan: {n} files (every Lean file and lakefile.toml) scanned for forbidden tokens')


def mathlib_rev(manifest):
    for p in json.load(open(manifest))['packages']:
        if p['name'] == 'mathlib':
            return p['rev']
    return None


def copy_tree(src, dst):
    """macOS clonefile, then Linux reflink, then a plain copy (the same ladder as scripts/gate.sh)."""
    for cmd in (['cp', '-Rc', src, dst], ['cp', '-R', '--reflink=auto', src, dst], ['cp', '-R', src, dst]):
        shutil.rmtree(dst, ignore_errors=True)
        if subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
            return
    raise Fatal(f'could not copy {src} to {dst}')


def stage_deps(obs):
    pk = os.path.join(PKG, '.lake', 'packages')
    if os.path.isdir(os.path.join(pk, 'mathlib')):
        log('deps: .lake/packages/mathlib present')
        return
    want = mathlib_rev(os.path.join(PKG, 'lake-manifest.json'))
    parent = os.path.join(PKG, '..', '.lake', 'packages')
    parent_manifest = os.path.join(PKG, '..', 'lake-manifest.json')
    if os.path.isdir(os.path.join(parent, 'mathlib')) and os.path.exists(parent_manifest) \
            and mathlib_rev(parent_manifest) == want:
        os.makedirs(os.path.join(PKG, '.lake'), exist_ok=True)
        log('deps: copying the parent repo\'s .lake/packages (clone or reflink where the filesystem allows)')
        copy_tree(parent, pk)
        return
    log('deps: no local Mathlib build; running lake exe cache get (network)')
    run(['lake', 'exe', 'cache', 'get'])


def stage_build(timing):
    shutil.rmtree(os.path.join(PKG, '.lake', 'build'), ignore_errors=True)
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '2'))
    for m in MODULES:
        rc, text, wall, rss = run(['lake', 'build', f'HashAgreement.{m}'], check=False, env=env)
        with open(os.path.join(BUILD, f'build-{m}.log'), 'w') as f:
            f.write(text)
        timing['build'][m] = {'wall_s': round(wall, 1), 'maxrss_kb': rss}
        if rc != 0:
            raise Fatal(f'BUILD FAILED HashAgreement.{m}:\n{text[-3000:]}')
        if re.search(r'declaration uses .sorry.|sorryAx', text):
            raise Fatal(f'SORRY reported while building HashAgreement.{m}')
        log(f'build HashAgreement.{m}: {wall:.1f} s, peak RSS {rss / 1024 / 1024:.2f} GiB')
    log(f'build: {len(MODULES)} modules, one at a time, LEAN_NUM_THREADS={env["LEAN_NUM_THREADS"]}')


def stage_census(obs, failures, timing):
    rc, text, wall, rss = run(['lake', 'env', 'lean', '-M4096', 'Census.lean'], check=False)
    with open(os.path.join(BUILD, 'census.jsonl'), 'w') as f:
        f.write(text)
    bad = [l for l in text.split('\n') if 'error' in l.lower() and not l.startswith('{')]
    if rc != 0 or bad:
        raise Fatal(f'CENSUS FAILED (rc {rc}):\n' + '\n'.join(bad[:20]))
    thms, aux = {}, 0
    for line in text.split('\n'):
        if not line.startswith('{'):
            continue
        r = json.loads(line)
        if r['kind'] != 'theorem':
            kind = {'axiomInfo': 'AXIOM', 'opaqueInfo': 'OPAQUE'}.get(r['kind'], r['kind'].upper())
            failures.append(f'{kind} DECLARED {r["name"]} in {r["module"]}')
            continue
        extra = sorted(set(r['axioms']) - ALLOWED_AXIOMS)
        if extra:
            failures.append(f'NON-STANDARD AXIOM {extra} in {r["name"]}')
        if any(AUX.match(c) for c in r['name'].split('.')):
            aux += 1
            continue
        if r['name'] in thms:
            failures.append(f'DUPLICATE theorem {r["name"]}')
        thms[r['name']] = {'module': r['module'], 'type': r['type'], 'axioms': r['axioms']}
    for n in HEADLINE:
        if n not in thms:
            failures.append(f'HEADLINE theorem missing from the census: {n}')
    obs['theorems'] = thms
    timing['census'] = {'wall_s': round(wall, 1), 'maxrss_kb': rss, 'declared': len(thms), 'auxiliary': aux}
    log(f'census: {len(thms)} declared theorems, {aux} auxiliary lemmas, standard axioms only ({wall:.0f} s)')


def stage_negative(obs, failures):
    rel = 'Neg/RoundsNeg.lean'
    rc, text, _, _ = run(['lake', 'env', 'lean', '-M4096', rel], check=False)
    with open(os.path.join(BUILD, 'neg-RoundsNeg.log'), 'w') as f:
        f.write(text)
    src = open(os.path.join(PKG, rel)).read().split('\n')
    start = next(i for i, l in enumerate(src, 1) if l.startswith('theorem round4_wrong '))
    errs = re.findall(r'^Neg/RoundsNeg\.lean:(\d+):(\d+): error: (.*)$', text, re.M)
    res = {'compiled': rc == 0, 'errors': [{'line': int(l), 'col': int(c), 'message': m} for l, c, m in errs]}
    if rc == 0:
        failures.append('NEGATIVE CONTROL COMPILED: Neg/RoundsNeg.lean')
    if len(errs) != 2:
        failures.append(f'NEGATIVE CONTROL: expected exactly 2 errors, got {len(errs)}')
    for l, c, m in errs:
        if int(l) <= start:
            failures.append(f'NEGATIVE CONTROL: error before round4_wrong at line {l}')
        if not m.startswith('Tactic `decide` proved that the proposition'):
            failures.append(f'NEGATIVE CONTROL: unexpected error kind at {l}:{c}: {m}')
    if not re.search(r'^is false$', text, re.M):
        failures.append('NEGATIVE CONTROL: no "is false" verdict in the output')
    obs['negative_control'] = res
    log(f'negative control: {len(errs)} errors, round4_wrong at line {start}, '
        + ', '.join(f'{l}:{c}' for l, c, _ in errs))


def stage_lean_vectors(obs, timing):
    rc, text, wall, rss = run(['lake', 'env', 'lean', '-M4096', 'test/Vectors.lean'], check=False)
    with open(os.path.join(BUILD, 'vectors.log'), 'w') as f:
        f.write(text)
    if rc != 0 or 'error' in text:
        raise Fatal(f'LEAN VECTOR TEST FAILED (rc {rc}):\n{text[-2000:]}')
    obs['lean_vectors'] = text.strip()
    timing['lean_vectors'] = {'wall_s': round(wall, 1), 'maxrss_kb': rss}
    log(f'lean vectors: {text.strip()} ({wall:.0f} s)')


# ---------------------------------------------------------------- comparison

def compare(obs, exp, failures):
    for s in sorted(set(exp) - set(SECTIONS)):
        failures.append(f'UNEXPECTED section {s} in expected.json')
    for s in SECTIONS:
        if s not in exp:
            failures.append(f'MISSING section {s} in expected.json')
            continue
        if s not in obs:
            failures.append(f'MISSING section {s} in the observed results (stage did not run)')
            continue
        e, o = exp[s], obs[s]
        if not isinstance(e, dict) or not isinstance(o, dict):
            if e != o:
                failures.append(f'MISMATCH {s}: expected {e!r}, got {o!r}')
            continue
        for k in sorted(set(e) - set(o)):
            failures.append(f'MISSING {s}: {k}')
        for k in sorted(set(o) - set(e)):
            failures.append(f'UNEXPECTED {s}: {k}')
        for k in sorted(set(e) & set(o)):
            if e[k] != o[k]:
                failures.append(f'MISMATCH {s}: {k}: expected {json.dumps(e[k], ensure_ascii=False)[:400]} '
                                f'got {json.dumps(o[k], ensure_ascii=False)[:400]}')
    for n in HEADLINE:
        if n not in exp.get('theorems', {}):
            failures.append(f'HEADLINE theorem missing from expected.json: {n}')


def check():
    t0 = time.monotonic()
    os.makedirs(BUILD, exist_ok=True)
    obs, failures, timing = {}, [], {'build': {}}
    try:
        stage_tools(obs)
        stage_inventory(obs)
        stage_inputs(obs)
        stage_sources()
        stage_regen(obs)
        stage_python_vectors(obs)
        stage_scan(failures)
        stage_deps(obs)
        stage_build(timing)
        stage_census(obs, failures, timing)
        stage_negative(obs, failures)
        stage_lean_vectors(obs, timing)
    except Fatal as e:
        failures.append(str(e))
    timing['total_wall_s'] = round(time.monotonic() - t0, 1)
    timing['build_wall_s'] = round(sum(v['wall_s'] for v in timing['build'].values()), 1)
    timing['build_maxrss_kb'] = max([v['maxrss_kb'] for v in timing['build'].values()] + [0])
    with open(os.path.join(BUILD, 'observed.json'), 'w') as f:
        json.dump({**{s: obs[s] for s in SECTIONS if s in obs}, 'timing': timing}, f, indent=1, ensure_ascii=False)
    exp_path = os.path.join(PKG, 'expected.json')
    if os.path.exists(exp_path):
        try:
            compare(obs, load_json_strict(exp_path), failures)
        except Fatal as e:
            failures.append(str(e))
    else:
        failures.append('expected.json is missing (build/observed.json holds this run; review it and copy it there)')
    print()
    print(f'build: {timing["build_wall_s"]} s wall over {len(timing["build"])} modules, peak RSS '
          f'{timing["build_maxrss_kb"] / 1024 / 1024:.2f} GiB; whole check {timing["total_wall_s"]} s')
    for m, v in timing['build'].items():
        print(f'  HashAgreement.{m}: {v["wall_s"]} s, {v["maxrss_kb"] / 1024 / 1024:.2f} GiB')
    if failures:
        print(f'\nREPLAY CHECK FAIL: {len(failures)} finding(s)')
        for x in failures:
            print(' -', x.split('\n')[0][:300])
            for more in x.split('\n')[1:12]:
                print('    ', more[:300])
        return 1
    n = len(obs['theorems'])
    print(f'REPLAY CHECK PASS: {n} theorems, standard axioms only; negative control failed at the '
          f'recorded places; 300 vectors agree in Python and in Lean')
    return 0


if __name__ == '__main__':
    if sys.argv[1:] == ['check']:
        sys.exit(check())
    print(__doc__)
    sys.exit(2)
