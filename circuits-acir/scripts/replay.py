#!/usr/bin/env python3
"""Replay check for the circuits-acir package (driven by ../check.sh).

usage: replay.py check              run every stage; exit 0 only if build/observed.json equals expected.json
       replay.py self-test          run the must-fail fixtures against copies of a passing tree
       replay.py compare-census F   compare census lines in F with expected.json (comparator only)

Stages of `check`: tool pins, source inventory, input artifacts, bytecode-to-print
comparison, regeneration of the Lean data, Python witness controls, forbidden-token scan, sequential Lean builds, theorem census
(statements, raw-type hashes and axioms of every theorem in an AcirLean module), negative
controls, and an
exact comparison with expected.json. Missing, duplicate and unexpected entries fail.
"""
import glob
import hashlib
import json
import lzma
import os
import re
import resource
import shutil
import subprocess
import sys
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
CIRCUITS = {
    'deposit': {'ns': 'Deposit', 'parts': 2, 'values': '2', 'rules': ['Amount'],
                'nv': '(solved 2).val = 500'},
    'withdraw': {'ns': 'Withdraw', 'parts': 3, 'values': '2', 'rules': ['Amount'],
                 'nv': '(solved 2).val = 700'},
    'transfer': {'ns': 'Transfer', 'parts': 5, 'values': '7,8,10,11,13,14,17,18,17906,17907',
                 'rules': ['Rules'],
                 'nv': '(solved 8).val = 1000 ∧ (solved 11).val = 0 ∧ (solved 14).val = 700 ∧ '
                       '(solved 18).val = 300 ∧ solved 10 = solved 7 ∧ solved 13 = solved 7 ∧ '
                       'solved 17 = solved 7'},
}
NV_GROUP = 4
TOKEN = 435537695816263162368054109405345813312609277316
# Python witness controls: (circuit, witness index, new value, opcode index that must fail).
PYTHON_CONTROLS = [
    ('deposit', 2, 2 ** 128, 23),
    ('deposit', 2, 501, None),
    ('deposit', 5, 7, None),
    ('withdraw', 2, 2 ** 128, 362),
    ('transfer', 18, 2 ** 128, 3),
    ('transfer', 8, 1001, 23535),
    ('transfer', 17, TOKEN + 1, 23542),
]
# The claims the README states. Each must be in expected.json and in the census.
HEADLINE = [
    'AcirLean.Deposit.amount_lt_two_pow_128', 'AcirLean.Deposit.satisfiable',
    'AcirLean.Withdraw.amount_lt_two_pow_128', 'AcirLean.Withdraw.satisfiable',
    'AcirLean.Transfer.amount_ranges', 'AcirLean.Transfer.conservation',
    'AcirLean.Transfer.token_consistency', 'AcirLean.Transfer.satisfiable',
]
SECTIONS = ['toolchain', 'source_files', 'inputs', 'bytecode_check', 'generated_files', 'extraction',
            'witness_check', 'python_controls', 'theorems', 'negative_controls']
GENERATED = re.compile(r'^AcirLean/(Deposit|Withdraw|Transfer)/(Data\.lean|Data\.lean\.json|'
                       r'Data/Part\d+\.lean|WitnessData\.lean|NV/G\d+\.lean|NonVacuity\.lean)$')
UNPINNED = {'README.md', 'expected.json', '.gitignore'}


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def log(msg):
    print(f'[{time.strftime("%H:%M:%S")}] {msg}', flush=True)


def run(cmd, out=None, check=True, env=None):
    p = subprocess.run(cmd, cwd=PKG, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = p.stdout.decode(errors='replace')
    if out:
        with open(out, 'w') as f:
            f.write(text)
    if check and p.returncode != 0:
        raise Fatal(f'command failed (rc {p.returncode}): {" ".join(cmd)}\n{text[-2000:]}')
    return p.returncode, text


class Fatal(Exception):
    pass


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
        dirs[:] = [d for d in dirs if d != '__pycache__' and not (rel_root == '.' and d in ('.lake', 'build'))]
        for f in files:
            rel = os.path.normpath(os.path.join(rel_root, f))
            out.append(rel)
    return sorted(out)


# ---------------------------------------------------------------- stages

def stage_tools(obs):
    with open(os.path.join(PKG, 'lean-toolchain')) as f:
        tc = f.read().strip()
    _, ver = run(['lake', '--version'])
    obs['toolchain'] = {'lean-toolchain': tc, 'lake_reports_lean_4_33_1': 'Lean version 4.33.1' in ver,
                        'python_ge_3_10': sys.version_info >= (3, 10)}
    log(f'tools: {tc}; {ver.strip()}; python {sys.version.split()[0]}')


def stage_inventory(obs):
    src = {}
    for rel in walk_files():
        if rel in UNPINNED or GENERATED.match(rel):
            continue
        src[rel] = sha(os.path.join(PKG, rel))
    obs['source_files'] = src
    log(f'inventory: {len(src)} pinned source files')


def func0_section(text):
    lines = text.split('\n')
    s = lines.index('func 0') + 1
    e = s
    while lines[e] != '':
        e += 1
    return ('\n'.join(lines[s:e]) + '\n').encode()


def stage_inputs(obs):
    d = os.path.join(BUILD, 'inputs')
    os.makedirs(d, exist_ok=True)
    res = {}
    for c in CIRCUITS:
        raw_print = lzma.decompress(open(os.path.join(PKG, 'inputs', f'{c}.acir.txt.xz'), 'rb').read())
        raw_art = lzma.decompress(open(os.path.join(PKG, 'inputs', f'{c}.json.xz'), 'rb').read())
        for name, data in ((f'{c}.acir.txt', raw_print), (f'{c}.json', raw_art)):
            p = os.path.join(d, name)
            if not (os.path.exists(p) and sha(p) == hashlib.sha256(data).hexdigest()):
                with open(p, 'wb') as f:
                    f.write(data)
        art = json.loads(raw_art)
        res[c] = {
            'print_sha256': hashlib.sha256(raw_print).hexdigest(),
            'func0_sha256': hashlib.sha256(func0_section(raw_print.decode())).hexdigest(),
            'artifact_sha256': hashlib.sha256(raw_art).hexdigest(),
            'bytecode_sha256': hashlib.sha256(art['bytecode'].encode()).hexdigest(),
            'noir_version': art.get('noir_version'),
            'witness_sha256': sha(os.path.join(PKG, 'inputs', f'{c}-witness.gz')),
        }
    obs['inputs'] = res
    log('inputs: decompressed and hashed ' + ', '.join(f'{c} func0 {v["func0_sha256"][:12]}' for c, v in res.items()))


def stage_bytecode(obs, failures):
    res = {}
    d = os.path.join(BUILD, 'inputs')
    for c in CIRCUITS:
        rc, text = run(['python3', 'scripts/bytecode_check.py', f'{d}/{c}.acir.txt', f'{d}/{c}.json'],
                       out=os.path.join(BUILD, f'{c}-bytecode-check.json'), check=False)
        try:
            res[c] = json.loads(text)
        except ValueError:
            res[c] = {'error': text[-400:]}
        if rc != 0:
            diffs = res[c].get('first_differences') or [res[c].get('error', text[-400:])]
            failures.extend(f'BYTECODE MISMATCH {c}: {x}' for x in diffs)
    obs['bytecode_check'] = res
    if any(l.startswith('BYTECODE MISMATCH') for l in failures):
        raise Fatal('the print differs from the artifact bytecode; nothing was regenerated or built')
    log('bytecode: ' + ', '.join(f'{c} {v["opcodes"]} opcodes match the print' for c, v in res.items()))


def generated_files():
    return {rel: sha(os.path.join(PKG, rel)) for rel in walk_files() if GENERATED.match(rel)}


def regen_key():
    h = hashlib.sha256()
    for rel in ['scripts/acir2lean.py', 'scripts/witness_check.py', 'scripts/gen_nv.py',
                'scripts/perturb_check.py', 'scripts/replay.py']:
        h.update(sha(os.path.join(PKG, rel)).encode())
    for c in CIRCUITS:
        for f in (f'{c}.acir.txt.xz', f'{c}.json.xz', f'{c}-witness.gz'):
            h.update(sha(os.path.join(PKG, 'inputs', f)).encode())
    return h.hexdigest()


def stage_regen(obs):
    stamp = os.path.join(BUILD, 'regen.json')
    key = regen_key()
    if os.path.exists(stamp):
        st = json.load(open(stamp))
        if st.get('key') == key and st.get('generated_files') == generated_files():
            obs.update({k: st[k] for k in ('generated_files', 'extraction', 'witness_check', 'python_controls')})
            log('regen: generated files and Python controls are current (same inputs, scripts and hashes)')
            return
    for rel in generated_files():
        os.remove(os.path.join(PKG, rel))
    ext, wc, pc = {}, {}, {}
    inp = os.path.join(BUILD, 'inputs')
    for c, cfg in CIRCUITS.items():
        ns = cfg['ns']
        t0 = time.time()
        data = f'AcirLean/{ns}/Data.lean'
        run(['python3', 'scripts/acir2lean.py', f'{inp}/{c}.acir.txt', f'{inp}/{c}.json', data, ns,
             '--parts', str(cfg['parts'])], out=os.path.join(BUILD, f'{c}-extract.json'))
        m = json.load(open(os.path.join(PKG, data + '.json')))
        ext[c] = {k: m[k] for k in ('func0_sha256', 'bytecode_sha256', 'artifact_sha256', 'noir_version',
                                    'counts', 'opcodes', 'chunk', 'chunks', 'parts', 'reprint_mismatches',
                                    'abi_layout_matches_print', 'max_witness')}
        ext[c]['ranges'] = len(m['ranges'])
        p = subprocess.run(['python3', 'scripts/witness_check.py', f'{inp}/{c}.acir.txt', f'{inp}/{c}.json',
                            f'inputs/{c}-witness.gz', '--lean', f'AcirLean/{ns}/WitnessData.lean', ns,
                            '--values', cfg['values']], cwd=PKG, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = p.stdout.decode(), p.stderr.decode()
        with open(os.path.join(BUILD, f'{c}-witness-check.txt'), 'w') as f:
            f.write(out + err)
        if p.returncode != 0:
            raise Fatal(f'witness check failed for {c}:\n{(out + err)[-2000:]}')
        r = json.loads(out)
        t = json.loads(err.strip().split('\n')[-1])
        wc[c] = {'witness_sha256': r['witness_sha256'], 'checked': r['checked'], 'failures': r['failures'],
                 'missing_witness_refs': r['missing_witness_refs'], 'values': r['values'],
                 'trie_depth': t['trie_depth'], 'trie_nodes': t['trie_nodes'],
                 'lookups_checked': t['lookups_checked']}
        run(['python3', 'scripts/gen_nv.py', '.', ns, data + '.json', str(NV_GROUP), cfg['nv']],
            out=os.path.join(BUILD, f'{c}-nv-mods.txt'))
        log(f'regen: {c} data ({ext[c]["opcodes"]} opcodes, {ext[c]["parts"]} parts), witness trie, '
            f'NV modules ({time.time() - t0:.0f} s)')
    for c, i, v, must in PYTHON_CONTROLS:
        cmd = ['python3', 'scripts/perturb_check.py', f'{inp}/{c}.acir.txt', f'inputs/{c}-witness.gz', str(i), str(v)]
        if must is not None:
            cmd.append(str(must))
        rc, text = run(cmd, check=False)
        r = json.loads(text)
        r['rc'] = rc
        pc[f'{c} w{i}={v}'] = r
    log(f'python controls: {len(pc)} mutated witnesses checked')
    obs['generated_files'] = generated_files()
    obs['extraction'], obs['witness_check'], obs['python_controls'] = ext, wc, pc
    with open(stamp, 'w') as f:
        json.dump({'key': key, **{k: obs[k] for k in ('generated_files', 'extraction', 'witness_check',
                                                      'python_controls')}}, f, indent=1)


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


def build_steps():
    steps = ['AcirLean.Semantics', 'AcirLean.Witness', 'AcirLean.Linear']
    for c, cfg in CIRCUITS.items():
        ns = cfg['ns']
        steps += [f'AcirLean.{ns}.Data.Part{j}' for j in range(cfg['parts'])]
        steps += [f'AcirLean.{ns}.Data'] + [f'AcirLean.{ns}.{r}' for r in cfg['rules']]
        steps += [f'AcirLean.{ns}.WitnessData', f'AcirLean.{ns}.Solved']
        steps += [l.strip() for l in open(os.path.join(BUILD, f'{c}-nv-mods.txt')) if l.strip()]
        steps += [f'AcirLean.{ns}.NonVacuity', f'AcirLean.{ns}.Controls']
    return steps


def stage_build(timings):
    steps = build_steps()
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '2'))
    finals = [f'AcirLean.{cfg["ns"]}.Controls' for cfg in CIRCUITS.values()]
    rc, _ = run(['lake', 'build', '--no-build'] + finals, check=False, env=env)
    if rc == 0:
        log(f'build: all {len(steps)} modules up to date (lake build --no-build)')
        return
    logd = os.path.join(BUILD, 'lean-logs')
    os.makedirs(logd, exist_ok=True)
    for k, mod in enumerate(steps, 1):
        t0 = time.time()
        rc, text = run(['lake', 'build', mod], out=os.path.join(logd, f'{mod}.log'), check=False, env=env)
        dt = time.time() - t0
        timings.append({'module': mod, 'wall_s': round(dt, 1), 'rc': rc})
        if rc != 0:
            raise Fatal(f'BUILD FAILED {mod}:\n{text[-3000:]}')
        if dt > 5:
            log(f'build {k}/{len(steps)} {mod}: {dt:.0f} s')
    log(f'build: {len(steps)} modules, one at a time, LEAN_NUM_THREADS={env["LEAN_NUM_THREADS"]}')


def parse_census(text, failures):
    thms, extra = {}, []
    for line in text.split('\n'):
        if not line.startswith('{'):
            continue
        r = json.loads(line)
        if r['kind'] == 'theorem':
            if r['name'] in thms:
                failures.append(f'DUPLICATE theorem {r["name"]}')
            thms[r['name']] = {'module': r['module'], 'type': r['type'],
                               'type_sha256': hashlib.sha256(r['raw'].encode()).hexdigest(),
                               'axioms': r['axioms']}
            if '⋯' in r['type']:
                failures.append(f'ELIDED statement of {r["name"]}: the census print contains ⋯')
            bad = sorted(set(r['axioms']) - ALLOWED_AXIOMS)
            if bad:
                failures.append(f'NON-STANDARD AXIOM {bad} in {r["name"]}')
        else:
            extra.append(r)
            kind = {'axiomInfo': 'AXIOM', 'opaqueInfo': 'OPAQUE'}.get(r['kind'], r['kind'].upper())
            failures.append(f'{kind} DECLARED {r["name"]} in {r["module"]}')
    return thms


def stage_census(obs, failures):
    t0 = time.time()
    rc, text = run(['lake', 'env', 'lean', '-M3600', 'Census.lean'], out=os.path.join(BUILD, 'census.jsonl'),
                   check=False)
    bad = [l for l in text.split('\n') if 'error' in l.lower() and not l.startswith('{')]
    if rc != 0 or bad:
        raise Fatal(f'CENSUS FAILED (rc {rc}):\n' + '\n'.join(bad[:20]))
    obs['theorems'] = parse_census(text, failures)
    log(f'census: {len(obs["theorems"])} theorems ({time.time() - t0:.0f} s)')


def stage_negatives(obs):
    res = {}
    for rel in sorted(glob.glob('Neg/*.lean', root_dir=PKG)):
        rc, text = run(['lake', 'env', 'lean', '-M3600', rel], check=False)
        first = next((l.strip() for l in text.split('\n') if 'error' in l), '')
        res[rel] = {'compiled': rc == 0, 'first_error': first}
        with open(os.path.join(BUILD, 'neg-' + os.path.basename(rel) + '.log'), 'w') as f:
            f.write(text)
    obs['negative_controls'] = res
    log(f'negative controls: {len(res)} files run, {sum(1 for v in res.values() if not v["compiled"])} failed as required')


# ---------------------------------------------------------------- comparison

def compare(obs, exp, failures, sections=SECTIONS):
    for s in sorted(set(exp) - set(sections)):
        failures.append(f'UNEXPECTED section {s} in expected.json')
    for s in sections:
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
    for name in HEADLINE:
        if name not in exp.get('theorems', {}):
            failures.append(f'MISSING headline theorem {name} in expected.json')
    for rel, v in obs.get('negative_controls', {}).items():
        if v['compiled']:
            failures.append(f'NEGATIVE CONTROL {rel} COMPILED')
    for k, v in obs.get('python_controls', {}).items():
        if v['required_opcode'] is not None and not v['required_fails']:
            failures.append(f'PYTHON CONTROL {k}: opcode {v["required_opcode"]} did not fail')


def check():
    os.makedirs(BUILD, exist_ok=True)
    for p in ('PASS', 'observed.json'):
        if os.path.exists(os.path.join(BUILD, p)):
            os.remove(os.path.join(BUILD, p))
    t_start = time.time()
    obs, failures, timings = {}, [], []
    exp = load_json_strict(os.path.join(PKG, 'expected.json'))
    try:
        stage_tools(obs)
        stage_inventory(obs)
        stage_inputs(obs)
        if obs['inputs'] != exp.get('inputs'):
            raise Fatal('input artifacts differ from expected.json; nothing was regenerated or built')
        stage_bytecode(obs, failures)
        stage_regen(obs)
        stage_scan(failures)
        stage_build(timings)
        stage_census(obs, failures)
        stage_negatives(obs)
    except Fatal as e:
        failures.append(f'FATAL {e}')
    compare(obs, exp, failures)
    with open(os.path.join(BUILD, 'observed.json'), 'w') as f:
        json.dump(obs, f, indent=1, ensure_ascii=False, sort_keys=True)
    with open(os.path.join(BUILD, 'timings.json'), 'w') as f:
        json.dump({'total_wall_s': round(time.time() - t_start, 1), 'steps': timings,
                   'max_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}, f, indent=1)
    if failures:
        print('\n'.join(failures))
        print(f'REPLAY CHECK FAIL: {len(failures)} problem(s); see build/observed.json')
        return 1
    with open(os.path.join(BUILD, 'PASS'), 'w') as f:
        f.write(time.strftime('%Y-%m-%dT%H:%M:%S%z') + '\n')
    th = obs['theorems']
    print('Headline statements (kernel-checked; axioms from the census):')
    for name in HEADLINE:
        print(f'  {name} : {th[name]["type"]}  [{", ".join(th[name]["axioms"])}]')
    print(f'REPLAY CHECK PASS: {len(obs["inputs"])} circuits (each print matches its bytecode), '
          f'{len(th)} theorems with pinned statements '
          f'and standard axioms only, {len(obs["negative_controls"])} negative Lean controls failed as '
          f'expected, {len(obs["python_controls"])} Python witness controls matched, '
          f'{time.time() - t_start:.0f} s')
    return 0


# ---------------------------------------------------------------- self-test

def edit(root, rel, old, new, count=1):
    p = os.path.join(root, rel)
    s = open(p, encoding='utf-8').read()
    if s.count(old) != count:
        raise SystemExit(f'self-test fixture cannot apply to {rel}: anchor found {s.count(old)} times')
    open(p, 'w', encoding='utf-8').write(s.replace(old, new))


def repin(root, rel):
    """Update the pinned hash of `rel`, so that only the deeper check can catch the change."""
    p = os.path.join(root, 'expected.json')
    e = json.load(open(p))
    e['source_files'][rel] = sha(os.path.join(root, rel))
    json.dump(e, open(p, 'w'), indent=1, ensure_ascii=False)


def fx_missing(root):
    edit(root, 'AcirLean/Transfer/Rules.lean', 'theorem token_names :', 'example :')
    repin(root, 'AcirLean/Transfer/Rules.lean')


def fx_unexpected(root):
    edit(root, 'AcirLean/Transfer/Rules.lean', 'end AcirLean.Transfer', 'theorem extra_fact : True := trivial\n\nend AcirLean.Transfer')
    repin(root, 'AcirLean/Transfer/Rules.lean')


def fx_weakened(root):
    edit(root, 'AcirLean/Deposit/Amount.lean',
         '    (w 2).val < 2 ^ 128 :=\n  Circuit.range_of_mem h range_amount_mem',
         '    (w 2).val < 2 ^ 129 :=\n  Nat.lt_trans (Circuit.range_of_mem h range_amount_mem) (by decide)')
    repin(root, 'AcirLean/Deposit/Amount.lean')


def fx_input(root):
    p = os.path.join(root, 'inputs', 'withdraw.acir.txt.xz')
    s = lzma.decompress(open(p, 'rb').read()).decode()
    lines = s.split('\n')
    k = lines.index('func 0') + 4 + 362
    if lines[k] != 'BLACKBOX::RANGE input: w2, bits: 128':
        raise SystemExit('self-test fixture cannot find withdraw opcode 362')
    lines[k] = 'BLACKBOX::RANGE input: w2, bits: 129'
    open(p, 'wb').write(lzma.compress('\n'.join(lines).encode(), preset=9))
    repin(root, 'inputs/withdraw.acir.txt.xz')


def fx_rogue_axiom(root):
    edit(root, 'AcirLean/Deposit/Amount.lean', 'import AcirLean.Deposit.Data\n',
         'import AcirLean.Deposit.Data\nimport Lean\n\n'
         'open Lean Elab Command in\nelab "rogue_decl" : command => liftCoreM <| addDecl (.axiomDecl '
         '{ name := `AcirLean.Deposit.rogue, levelParams := [], type := mkConst ``False, isUnsafe := false })\n\n'
         'rogue_decl\n')
    edit(root, 'AcirLean/Deposit/Amount.lean',
         'circuit.publicParams[2]? = some 2 ∧ paramNames[2]? = some "amount" :=\n  ⟨rfl, rfl⟩',
         'circuit.publicParams[2]? = some 2 ∧ paramNames[2]? = some "amount" :=\n  AcirLean.Deposit.rogue.elim')
    repin(root, 'AcirLean/Deposit/Amount.lean')


def fx_skip_kernel(root):
    # A false membership claim (opcode 23542 is `ASSERT w17 = w7`): only the kernel rejects
    # it (Neg/TransferTokenSwap.lean), and the option turns the kernel check off.
    edit(root, 'AcirLean/Transfer/Rules.lean', 'end AcirLean.Transfer',
         'set_option debug.skipKernelTC true in\n'
         'theorem token_swap_mem : Opcode.assertZero (some 17) ⟨[], [(1, 18)], 0⟩ ∈ circuit.opcodes :=\n'
         '  List.mem_of_getElem? (l := opcodes) (i := 23542) (by decide +kernel)\n\nend AcirLean.Transfer')
    repin(root, 'AcirLean/Transfer/Rules.lean')


def repin_print(root, c):
    """Update every pinned hash of the print of circuit `c`, so that only the bytecode
    comparison can catch the change."""
    raw = lzma.decompress(open(os.path.join(root, 'inputs', f'{c}.acir.txt.xz'), 'rb').read())
    p = os.path.join(root, 'expected.json')
    e = json.load(open(p))
    e['inputs'][c]['print_sha256'] = hashlib.sha256(raw).hexdigest()
    e['inputs'][c]['func0_sha256'] = hashlib.sha256(func0_section(raw.decode())).hexdigest()
    json.dump(e, open(p, 'w'), indent=1, ensure_ascii=False)
    repin(root, f'inputs/{c}.acir.txt.xz')


def edit_print(root, c, k, line, new):
    p = os.path.join(root, 'inputs', f'{c}.acir.txt.xz')
    lines = lzma.decompress(open(p, 'rb').read()).decode().split('\n')
    f0 = lines.index('func 0') + 4
    if lines[f0 + k] != line:
        raise SystemExit(f'self-test fixture cannot find {c} opcode {k}')
    lines[f0 + k:f0 + k + 1] = [new] if new is not None else []
    open(p, 'wb').write(lzma.compress('\n'.join(lines).encode(), preset=9))
    repin_print(root, c)


def fx_print_changed(root):
    edit_print(root, 'withdraw', 362, 'BLACKBOX::RANGE input: w2, bits: 128', 'BLACKBOX::RANGE input: w2, bits: 127')


def fx_print_dropped(root):
    edit_print(root, 'deposit', 23, 'BLACKBOX::RANGE input: w2, bits: 128', None)


def fx_sorry(root):
    edit(root, 'AcirLean/Transfer/Rules.lean', '  ⟨rfl, rfl, rfl, rfl⟩\n\nend AcirLean.Transfer',
         '  sorry\n\nend AcirLean.Transfer')
    repin(root, 'AcirLean/Transfer/Rules.lean')


def fx_neg_compiles(root):
    edit(root, 'Neg/WithdrawBound127.lean', '(w 2).val < 2 ^ 127 :=', '(w 2).val < 2 ^ 128 :=')
    repin(root, 'Neg/WithdrawBound127.lean')


def fx_neg_wrong_reason(root):
    edit(root, 'Neg/TransferTokenSwap.lean', '(i := 23542) (by decide +kernel)', '(i := 23542) (by decide +kernel')
    repin(root, 'Neg/TransferTokenSwap.lean')


# (name, fixture, required failure lines, options). Options: `rebless` copies the census
# entries of the named theorems and their auxiliary lemmas (`decide +kernel` adds one) from
# the first run's observed.json into expected.json and runs the check again (an author
# re-blessing expected.json); `only` requires that every failure line matches one of the
# required patterns.
FIXTURES = [
    ('baseline-unchanged-copy', None, None),
    ('missing-theorem', fx_missing, [r'^MISSING theorems: AcirLean\.Transfer\.token_names$']),
    ('unexpected-theorem', fx_unexpected, [r'^UNEXPECTED theorems: AcirLean\.Transfer\.extra_fact$']),
    ('weakened-statement', fx_weakened, [r'^MISMATCH theorems: AcirLean\.Deposit\.amount_lt_two_pow_128: .*2 \^ 128.*2 \^ 129']),
    ('altered-input-artifact', fx_input, [r'^MISMATCH inputs: withdraw: ', r'^FATAL input artifacts differ']),
    ('rogue-axiom', fx_rogue_axiom, [r'^AXIOM DECLARED AcirLean\.Deposit\.rogue in AcirLean\.Deposit\.Amount$',
                                     r"^NON-STANDARD AXIOM \['AcirLean\.Deposit\.rogue'\] in AcirLean\.Deposit\.amount_is_public_input_2$"]),
    ('sorry-proof', fx_sorry, [r"^FORBIDDEN TOKEN 'sorry' at AcirLean/Transfer/Rules\.lean:",
                               r"^NON-STANDARD AXIOM \['sorryAx'\] in AcirLean\.Transfer\.token_names$"]),
    ('negative-control-compiles', fx_neg_compiles, [r'^NEGATIVE CONTROL Neg/WithdrawBound127\.lean COMPILED$']),
    ('negative-control-wrong-reason', fx_neg_wrong_reason, [r'^MISMATCH negative_controls: Neg/TransferTokenSwap\.lean: ']),
    ('kernel-check-skipped', fx_skip_kernel, [r"^FORBIDDEN TOKEN 'skipKernelTC' at AcirLean/Transfer/Rules\.lean:"],
     {'rebless': ['AcirLean.Transfer.token_swap_mem'], 'only': True}),
    ('print-differs-from-bytecode', fx_print_changed,
     [r"^BYTECODE MISMATCH withdraw: opcode 362: bytecode \('range', 2, 128\), print \('range', 2, 127\)$",
      r'^FATAL the print differs from the artifact bytecode']),
    ('print-drops-an-opcode', fx_print_dropped,
     [r'^BYTECODE MISMATCH deposit: opcode count: bytecode 7662, print 7661$',
      r'^FATAL the print differs from the artifact bytecode']),
]


def self_test():
    if not os.path.exists(os.path.join(BUILD, 'PASS')):
        log('self-test: no passing run in build/; running the check first')
        if check() != 0:
            print('SELF-TEST NOT RUN: the unmodified package does not pass')
            return 1
    results, bad = [], []
    # Comparator-only fixture: a duplicated census line.
    lines = open(os.path.join(BUILD, 'census.jsonl')).read().split('\n')
    first = next(l for l in lines if l.startswith('{'))
    f = []
    parse_census('\n'.join(lines + [first]), f)
    ok = any(x.startswith('DUPLICATE theorem ') for x in f)
    results.append({'fixture': 'duplicate-census-entry (comparator only)', 'ok': ok, 'failures': f})
    (log if ok else bad.append)(f'self-test duplicate-census-entry: {"caught" if ok else "NOT CAUGHT"}')
    # Copies live in build/selftest, on the same file system, so that `cp --reflink=auto`
    # can share the built .lake tree instead of copying it.
    tmp = os.path.join(BUILD, 'selftest')
    shutil.rmtree(tmp, ignore_errors=True)
    try:
        for name, fx, want, *opt in FIXTURES:
            opt = opt[0] if opt else {}
            root = os.path.join(tmp, name)
            os.makedirs(os.path.join(root, 'build'))
            for e in os.listdir(PKG):
                if e != 'build':
                    subprocess.run(['cp', '-a', '--reflink=auto', os.path.join(PKG, e), root], check=True)
            for e in os.listdir(BUILD):
                if e != 'selftest':
                    subprocess.run(['cp', '-a', '--reflink=auto', os.path.join(BUILD, e), os.path.join(root, 'build')],
                                   check=True)
            for p in ('PASS', 'observed.json'):
                if os.path.exists(os.path.join(root, 'build', p)):
                    os.remove(os.path.join(root, 'build', p))
            if fx:
                fx(root)
            t0 = time.time()
            p = subprocess.run(['python3', 'scripts/replay.py', 'check'], cwd=root,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            reblessed = {}
            if opt.get('rebless'):
                ob = json.load(open(os.path.join(root, 'build', 'observed.json')))
                ep = os.path.join(root, 'expected.json')
                e = json.load(open(ep))
                for t, v in ob.get('theorems', {}).items():
                    if any(t == r or t.startswith(r + '.') for r in opt['rebless']):
                        e['theorems'][t] = reblessed[t] = v
                json.dump(e, open(ep, 'w'), indent=1, ensure_ascii=False)
                p = subprocess.run(['python3', 'scripts/replay.py', 'check'], cwd=root,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            out = p.stdout.decode(errors='replace')
            fails = [l for l in out.split('\n') if re.match(r'^(MISSING|UNEXPECTED|MISMATCH|DUPLICATE|FATAL|'
                                                            r'FORBIDDEN|NON-STANDARD|AXIOM|OPAQUE|NEGATIVE|PYTHON|'
                                                            r'ELIDED|BYTECODE)', l)]
            if fx is None:
                ok = p.returncode == 0 and not fails
            else:
                ok = p.returncode != 0 and all(any(re.search(w, l) for l in fails) for w in want)
                if opt.get('only'):
                    ok = ok and all(any(re.search(w, l) for w in want) for l in fails)
            results.append({'fixture': name, 'ok': ok, 'rc': p.returncode, 'wall_s': round(time.time() - t0, 1),
                            'required': want, 'failures': fails, **({'reblessed': reblessed} if reblessed else {})})
            with open(os.path.join(BUILD, f'selftest-{name}.log'), 'w') as fh:
                fh.write(out)
            msg = f'self-test {name}: rc {p.returncode}, {"as intended" if ok else "WRONG"} ({time.time() - t0:.0f} s)'
            log(msg) if ok else (log(msg), bad.append(name))
            for l in fails[:6]:
                print(f'    {l[:240]}')
            shutil.rmtree(root)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    with open(os.path.join(BUILD, 'selftest.json'), 'w') as f:
        json.dump(results, f, indent=1, ensure_ascii=False)
    if bad:
        print(f'SELF-TEST FAIL: {bad}')
        return 1
    print(f'SELF-TEST PASS: the unchanged copy passes; {len(results) - 1} fixtures fail for their intended reason')
    return 0


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'check':
        return check()
    if len(sys.argv) >= 2 and sys.argv[1] == 'self-test':
        return self_test()
    if len(sys.argv) == 3 and sys.argv[1] == 'compare-census':
        f = []
        thms = parse_census(open(sys.argv[2]).read(), f)
        compare({'theorems': thms}, {'theorems': load_json_strict(os.path.join(PKG, 'expected.json'))['theorems']}, f,
                sections=('theorems',))
        print('\n'.join(f) or 'census matches')
        return 1 if f else 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
