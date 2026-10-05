#!/usr/bin/env python3
"""Translate `noir-inspector print-acir` output (Noir 1.0.0-beta.21) into Lean data.

usage: acir2lean.py <print-acir.txt> <artifact.json> <out.lean> <LeanNamespace> [--chunk N] [--parts K]

Accepts only the opcode forms of AcirLean.Semantics (ASSERT, BLACKBOX::RANGE, BRILLIG CALL)
and only a program with one ACIR function (`func 0`). Every opcode line is re-printed from
the parsed form with the beta.21 Display rules and must equal the input line byte for byte.
Also writes <out.lean>.json with hashes, counts and the ABI-to-witness layout check.

With --parts K, the chunks go to K modules <dir of out.lean>/Data/Part<j>.lean
(module AcirLean.<NS>.Data.Part<j>), and <out.lean> becomes a small module that imports the
parts and assembles `opcodes`, `circuit`, `publicNames` and `paramNames`. The data
definitions are `noncomputable`: the kernel reduces them, no compiled code is needed.
Without --parts the output is one module, the original single-module form.
"""
import hashlib
import json
import os
import re
import sys

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617

TERM_RE = re.compile(r'^(?:(\d+)\*)?w(\d+)(?:\*w(\d+))?$')
CONST_RE = re.compile(r'^\d+$')
RANGE_RE = re.compile(r'^BLACKBOX::RANGE input: w(\d+), bits: (\d+)$')
BRILLIG_RE = re.compile(r'^BRILLIG CALL func: (\d+), predicate: (.*), inputs: \[(.*)\], outputs: \[(.*)\]$')
ASSERT_RE = re.compile(r'^ASSERT (0|w\d+) = (.*)$')
PARAMS_RE = re.compile(r'^(private parameters|public parameters|return values): \[(.*)\]$')


def die(msg):
    sys.exit(f"acir2lean: {msg}")


def parse_wlist(s):
    s = s.strip()
    if s == '':
        return []
    out = []
    for x in s.split(', '):
        if not re.fullmatch(r'w\d+', x):
            die(f"bad witness list item {x!r}")
        out.append(int(x[1:]))
    return out


def parse_rhs(s, lineno):
    """Split at top-level ' + ' / ' - ' and parse each signed term."""
    pieces = re.split(r' ([+-]) ', s)
    first = pieces[0]
    signed = []
    if first.startswith('-'):
        signed.append((-1, first[1:]))
    else:
        signed.append((1, first))
    for i in range(1, len(pieces), 2):
        signed.append((1 if pieces[i] == '+' else -1, pieces[i + 1]))
    mul, lin, const = [], [], None
    for idx, (sg, body) in enumerate(signed):
        m = TERM_RE.match(body)
        if m:
            if const is not None:
                die(f"line {lineno}: term after constant")
            c = sg * (int(m.group(1)) if m.group(1) else 1)
            if m.group(3) is not None:
                if lin:
                    die(f"line {lineno}: product term after linear term")
                mul.append((c, int(m.group(2)), int(m.group(3))))
            else:
                lin.append((c, int(m.group(2))))
        elif CONST_RE.match(body):
            if idx != len(signed) - 1:
                die(f"line {lineno}: constant not last")
            const = sg * int(body)
        else:
            die(f"line {lineno}: cannot parse term {body!r}")
    return mul, lin, (0 if const is None else const)


def fmt_term(coef, ws, first):
    wstr = '*'.join(f'w{w}' for w in ws)
    if first:
        if coef == 1:
            return wstr
        if coef == -1:
            return '-' + wstr
        return f'{coef}*{wstr}'
    sign = ' - ' if coef < 0 else ' + '
    a = abs(coef)
    return sign + (wstr if a == 1 else f'{a}*{wstr}')


def reprint_assert(lhs, mul, lin, const):
    out = 'ASSERT ' + ('0' if lhs is None else f'w{lhs}') + ' = '
    printed = False
    for (c, i, j) in mul:
        out += fmt_term(c, [i, j], not printed)
        printed = True
    for (c, i) in lin:
        out += fmt_term(c, [i], not printed)
        printed = True
    if const == 0:
        if not printed:
            out += '0'
    else:
        if printed:
            out += (' - ' if const < 0 else ' + ') + str(abs(const))
        else:
            out += str(const)
    return out


def lean_int(c):
    return f'({c})' if c < 0 else str(c)


def lean_op(op):
    if op[0] == 'assert':
        _, lhs, mul, lin, const = op
        lhs_s = 'none' if lhs is None else f'(some {lhs})'
        mul_s = ', '.join(f'({lean_int(c)}, {i}, {j})' for (c, i, j) in mul)
        lin_s = ', '.join(f'({lean_int(c)}, {i})' for (c, i) in lin)
        return f'  .assertZero {lhs_s} ⟨[{mul_s}], [{lin_s}], {lean_int(const)}⟩'
    if op[0] == 'range':
        return f'  .range {op[1]} {op[2]}'
    outs = ', '.join(str(o) for o in op[2])
    return f'  .brilligCall {op[1]} [{outs}]'


def abi_names(prefix, t):
    k = t['kind']
    if k in ('field', 'integer', 'boolean'):
        return [prefix]
    if k == 'array':
        return [n for i in range(t['length']) for n in abi_names(f'{prefix}[{i}]', t['type'])]
    if k == 'struct':
        return [n for f in t['fields'] for n in abi_names(f'{prefix}.{f["name"]}', f['type'])]
    if k == 'tuple':
        return [n for i, f in enumerate(t['fields']) for n in abi_names(f'{prefix}.{i}', f)]
    if k == 'string':
        return [f'{prefix}[{i}]' for i in range(t['length'])]
    die(f"unknown ABI kind {k}")


def main():
    args = sys.argv[1:]
    chunk = 256
    parts = 0
    if '--chunk' in args:
        k = args.index('--chunk')
        chunk = int(args[k + 1])
        del args[k:k + 2]
    if '--parts' in args:
        k = args.index('--parts')
        parts = int(args[k + 1])
        del args[k:k + 2]
    if len(args) != 4:
        die(__doc__)
    txt_path, art_path, out_path, ns = args
    raw = open(txt_path, 'rb').read()
    lines = raw.decode().split('\n')
    # Locate func 0; refuse programs with more than one ACIR function.
    funcs = [i for i, l in enumerate(lines) if re.fullmatch(r'func \d+', l)]
    if len(funcs) != 1 or lines[funcs[0]] != 'func 0':
        die(f"expected exactly one ACIR function, found {len(funcs)}")
    start = funcs[0] + 1
    end = start
    while end < len(lines) and lines[end] != '':
        end += 1
    body = lines[start:end]
    func0_text = ('\n'.join(body) + '\n').encode()
    header = {}
    for l in body[:3]:
        m = PARAMS_RE.match(l)
        if not m:
            die(f"bad header line {l!r}")
        header[m.group(1)] = parse_wlist(m.group(2))
    ops = []
    counts = {'assert': 0, 'range': 0, 'brillig': 0}
    mismatches = 0
    for n, l in enumerate(body[3:], start=start + 4):
        if l.startswith('ASSERT '):
            m = ASSERT_RE.match(l)
            if not m:
                die(f"line {n}: bad ASSERT")
            lhs = None if m.group(1) == '0' else int(m.group(1)[1:])
            mul, lin, const = parse_rhs(m.group(2), n)
            if reprint_assert(lhs, mul, lin, const) != l:
                mismatches += 1
                die(f"line {n}: reprint mismatch")
            ops.append(('assert', lhs, mul, lin, const))
            counts['assert'] += 1
        elif l.startswith('BLACKBOX::'):
            m = RANGE_RE.match(l)
            if not m:
                die(f"line {n}: unsupported black box {l[:60]!r}")
            i, b = int(m.group(1)), int(m.group(2))
            if f'BLACKBOX::RANGE input: w{i}, bits: {b}' != l:
                die(f"line {n}: reprint mismatch")
            ops.append(('range', i, b))
            counts['range'] += 1
        elif l.startswith('BRILLIG CALL '):
            m = BRILLIG_RE.match(l)
            if not m:
                die(f"line {n}: bad BRILLIG CALL")
            outs = parse_wlist(m.group(4))
            ops.append(('brillig', int(m.group(1)), outs))
            counts['brillig'] += 1
        else:
            die(f"line {n}: unsupported opcode {l[:60]!r}")
    # Coefficients must be printed field representatives: |c| < P.
    for op in ops:
        if op[0] == 'assert':
            for t in op[2] + op[3]:
                if abs(t[0]) >= P:
                    die("coefficient out of range")
            if abs(op[4]) >= P:
                die("constant out of range")
    # ABI layout: flattened parameter sizes, in ABI order, give witness indices 0..n-1.
    art_bytes = open(art_path, 'rb').read()
    art = json.loads(art_bytes)

    def size(t):
        k = t['kind']
        if k in ('field', 'integer', 'boolean'):
            return 1
        if k == 'array':
            return t['length'] * size(t['type'])
        if k == 'struct':
            return sum(size(f['type']) for f in t['fields'])
        if k == 'tuple':
            return sum(size(f) for f in t['fields'])
        if k == 'string':
            return t['length']
        die(f"unknown ABI kind {k}")
    layout = []
    idx = 0
    param_names = []
    for p in art['abi']['parameters']:
        s = size(p['type'])
        nm = abi_names(p['name'], p['type'])
        if len(nm) != s:
            die("ABI name flattening disagrees with the ABI size")
        param_names += nm
        layout.append({'name': p['name'], 'visibility': p['visibility'], 'kind': p['type']['kind'],
                       'type': p['type'], 'witnesses': [idx, idx + s - 1]})
        idx += s
    pub = [w for q in layout if q['visibility'] == 'public' for w in range(q['witnesses'][0], q['witnesses'][1] + 1)]
    priv = [w for q in layout if q['visibility'] != 'public' for w in range(q['witnesses'][0], q['witnesses'][1] + 1)]
    layout_ok = (pub == header['public parameters'] and priv == header['private parameters'])
    if not layout_ok:
        die("ABI layout does not match the printed parameter lists")
    pub_names = [q['name'] for q in layout if q['visibility'] == 'public']

    def lst(xs):
        return '[' + ', '.join(str(x) for x in xs) + ']'

    src_note = [f'Source print sha256 (func 0 section): {hashlib.sha256(func0_text).hexdigest()}',
                f'Artifact bytecode sha256 (base64 string): {hashlib.sha256(art["bytecode"].encode()).hexdigest()}',
                f'noir_version: {art.get("noir_version")} -/']
    nchunks = (len(ops) + chunk - 1) // chunk
    names = [f'chunk{c}' for c in range(nchunks)]

    def chunk_defs(c_lo, c_hi, noncomp):
        L = []
        for c in range(c_lo, c_hi):
            kw = 'noncomputable def' if noncomp else 'def'
            L.append(f'{kw} chunk{c} : List Opcode := [')
            L.append(',\n'.join(lean_op(op) for op in ops[c * chunk:(c + 1) * chunk]))
            L.append(']')
            L.append('')
        return L

    def tail_defs(noncomp):
        kw = 'noncomputable def' if noncomp else 'def'
        if noncomp:
            # parts mode: right-nested, so that `opcodes[i]?` walks each chunk once
            body = '  ' + ' ++\n  ('.join(names) + ')' * (len(names) - 1)
        else:
            body = '  ' + ' ++\n  '.join(names)
        L = [f'{kw} opcodes : List Opcode :=', body, '',
             f'{kw} circuit : Circuit where',
             f'  privateParams := {lst(header["private parameters"])}',
             f'  publicParams := {lst(header["public parameters"])}',
             f'  returnValues := {lst(header["return values"])}',
             '  opcodes := opcodes', '',
             '/-- Public ABI parameter names, in ABI order (from the artifact; checked by the',
             '    extractor against the printed public parameter list). -/',
             'def publicNames : List String := [' + ', '.join(json.dumps(x) for x in pub_names) + ']', '',
             '/-- Flattened ABI parameter names: entry `i` names witness `i` (the extractor checks',
             '    that the flattened ABI sizes give the printed parameter lists). -/',
             'def paramNames : List String := [' + ', '.join(json.dumps(x) for x in param_names) + ']', '']
        return L

    files = {}
    part_of_chunk = {}
    if parts <= 0:
        L = ['import AcirLean.Semantics', '', '/-! Generated by scripts/acir2lean.py. Do not edit.'] + src_note
        L += ['', 'set_option maxRecDepth 16384', '', f'namespace AcirLean.{ns}', '', 'open AcirLean', '']
        L += chunk_defs(0, nchunks, False)
        L += tail_defs(False)
        L += [f'end AcirLean.{ns}', '']
        files[out_path] = '\n'.join(L)
        for c in range(nchunks):
            part_of_chunk[c] = None
    else:
        per = (nchunks + parts - 1) // parts
        pdir = os.path.join(os.path.dirname(out_path), 'Data')
        os.makedirs(pdir, exist_ok=True)
        imports = []
        for j in range(parts):
            c_lo, c_hi = j * per, min(nchunks, (j + 1) * per)
            if c_lo >= c_hi:
                die("too many parts for the chunk count")
            mod = f'AcirLean.{ns}.Data.Part{j}'
            imports.append(mod)
            L = ['import AcirLean.Semantics', '',
                 f'/-! Generated by scripts/acir2lean.py --parts {parts}. Do not edit.',
                 f'Part {j} of {parts}: chunks {c_lo} to {c_hi - 1}, opcodes {c_lo * chunk} to '
                 f'{min(len(ops), c_hi * chunk) - 1} of {len(ops)} (chunk size {chunk}).'] + src_note
            L += ['', 'set_option maxRecDepth 16384', '', f'namespace AcirLean.{ns}', '', 'open AcirLean', '']
            L += chunk_defs(c_lo, c_hi, True)
            L += [f'end AcirLean.{ns}', '']
            files[os.path.join(pdir, f'Part{j}.lean')] = '\n'.join(L)
            for c in range(c_lo, c_hi):
                part_of_chunk[c] = j
        L = [f'import {m}' for m in imports]
        L += ['', f'/-! Generated by scripts/acir2lean.py --parts {parts}. Do not edit.',
              f'Assembles the {nchunks} chunks of the {parts} part modules.'] + src_note
        L += ['', f'namespace AcirLean.{ns}', '', 'open AcirLean', '']
        L += tail_defs(True)
        L += [f'end AcirLean.{ns}', '']
        files[out_path] = '\n'.join(L)
    for path, text in files.items():
        with open(path, 'w') as f:
            f.write(text)
    # Index of each RANGE opcode, for the proofs.
    ranges = [(k, op[1], op[2]) for k, op in enumerate(ops) if op[0] == 'range']
    rel = {p: (os.path.relpath(p, os.path.dirname(out_path))) for p in files}
    meta = {
        'print_sha256_full': hashlib.sha256(raw).hexdigest(),
        'func0_sha256': hashlib.sha256(func0_text).hexdigest(),
        'artifact_sha256': hashlib.sha256(art_bytes).hexdigest(),
        'bytecode_sha256': hashlib.sha256(art['bytecode'].encode()).hexdigest(),
        'noir_version': art.get('noir_version'),
        'counts': counts,
        'opcodes': len(ops),
        'chunk': chunk,
        'chunks': nchunks,
        'parts': parts,
        'part_of_chunk': part_of_chunk,
        'reprint_mismatches': mismatches,
        'reprinted_lines': len(ops),
        'abi_layout': layout,
        'abi_layout_matches_print': layout_ok,
        'param_names': param_names,
        'max_witness': max([w for op in ops if op[0] == 'assert' for w in ([op[1]] if op[1] is not None else []) + [x for t in op[2] for x in t[1:]] + [t[1] for t in op[3]]] + [0]),
        'ranges': ranges,
        'lean_files': {rel[p]: {'sha256': hashlib.sha256(t.encode()).hexdigest(), 'bytes': len(t.encode())}
                       for p, t in files.items()},
        'lean_sha256': hashlib.sha256(files[out_path].encode()).hexdigest(),
    }
    json.dump(meta, open(out_path + '.json', 'w'), indent=1)
    print(json.dumps({k: v for k, v in meta.items() if k not in ('abi_layout', 'ranges', 'param_names', 'part_of_chunk')}, indent=1))


if __name__ == '__main__':
    main()
