#!/usr/bin/env python3
"""Check a solved witness (nargo execute, beta.21 msgpack-compact) against the parsed ACIR.

usage: witness_check.py <print-acir.txt> <artifact.json> <witness.gz> [--lean <out.lean> <Namespace>]
       [--split-depth S] [--values i,j,...]

Parses the print with acir2lean's parser (same file, same rules), decodes the witness stack,
and evaluates every opcode with Python integers: ASSERT as (lhs - rhs) mod P == 0, RANGE as
value < 2^bits. With --lean, also writes the witness as Lean data (a binary trie).
"""
import gzip
import hashlib
import importlib.util
import json
import os
import struct
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('acir2lean', os.path.join(here, 'acir2lean.py'))
a2l = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a2l)
P = a2l.P


def unpack(b, i):
    t = b[i]
    if t <= 0x7f:
        return t, i + 1
    if 0x80 <= t <= 0x8f:
        return unpack_map(b, i + 1, t & 0x0f)
    if 0x90 <= t <= 0x9f:
        return unpack_arr(b, i + 1, t & 0x0f)
    if 0xa0 <= t <= 0xbf:
        n = t & 0x1f
        return b[i + 1:i + 1 + n].decode(), i + 1 + n
    if t == 0xc0:
        return None, i + 1
    if t in (0xc2, 0xc3):
        return t == 0xc3, i + 1
    if t in (0xc4, 0xc5, 0xc6):
        w = {0xc4: 1, 0xc5: 2, 0xc6: 4}[t]
        n = int.from_bytes(b[i + 1:i + 1 + w], 'big')
        s = i + 1 + w
        return bytes(b[s:s + n]), s + n
    if t in (0xcc, 0xcd, 0xce, 0xcf):
        w = {0xcc: 1, 0xcd: 2, 0xce: 4, 0xcf: 8}[t]
        return int.from_bytes(b[i + 1:i + 1 + w], 'big'), i + 1 + w
    if t in (0xd0, 0xd1, 0xd2, 0xd3):
        w = {0xd0: 1, 0xd1: 2, 0xd2: 4, 0xd3: 8}[t]
        return int.from_bytes(b[i + 1:i + 1 + w], 'big', signed=True), i + 1 + w
    if t in (0xd9, 0xda, 0xdb):
        w = {0xd9: 1, 0xda: 2, 0xdb: 4}[t]
        n = int.from_bytes(b[i + 1:i + 1 + w], 'big')
        s = i + 1 + w
        return b[s:s + n].decode(), s + n
    if t in (0xdc, 0xdd):
        w = {0xdc: 2, 0xdd: 4}[t]
        return unpack_arr(b, i + 1 + w, int.from_bytes(b[i + 1:i + 1 + w], 'big'))
    if t in (0xde, 0xdf):
        w = {0xde: 2, 0xdf: 4}[t]
        return unpack_map(b, i + 1 + w, int.from_bytes(b[i + 1:i + 1 + w], 'big'))
    if t >= 0xe0:
        return t - 0x100, i + 1
    raise ValueError(f"unsupported msgpack type 0x{t:02x} at {i}")


def unpack_arr(b, i, n):
    out = []
    for _ in range(n):
        v, i = unpack(b, i)
        out.append(v)
    return out, i


def unpack_map(b, i, n):
    out = {}
    for _ in range(n):
        k, i = unpack(b, i)
        v, i = unpack(b, i)
        out[k] = v
    return out, i


def decode_witness(path):
    raw = gzip.open(path).read()
    if raw[0] != 3:
        sys.exit(f"witness format byte {raw[0]} != 3 (msgpack-compact)")
    val, end = unpack(raw, 1)
    if end != len(raw):
        sys.exit("trailing bytes in witness")
    stack = val[0]
    if len(stack) != 1 or stack[0][0] != 0:
        sys.exit("expected one stack item for function 0")
    wmap = stack[0][1]
    out = {}
    for k, v in wmap.items():
        if not isinstance(v, bytes) or len(v) != 32:
            sys.exit("unexpected field encoding")
        x = int.from_bytes(v, 'big')
        if x >= P:
            sys.exit("non-canonical field element")
        out[k] = x
    return out


def parse_ops(txt_path):
    lines = open(txt_path).read().split('\n')
    s = lines.index('func 0') + 1
    e = s
    while lines[e] != '':
        e += 1
    ops = []
    for n, l in enumerate(lines[s + 3:e]):
        if l.startswith('ASSERT '):
            m = a2l.ASSERT_RE.match(l)
            lhs = None if m.group(1) == '0' else int(m.group(1)[1:])
            ops.append(('assert', lhs) + a2l.parse_rhs(m.group(2), n))
        elif l.startswith('BLACKBOX::'):
            m = a2l.RANGE_RE.match(l)
            ops.append(('range', int(m.group(1)), int(m.group(2))))
        else:
            m = a2l.BRILLIG_RE.match(l)
            ops.append(('brillig', int(m.group(1)), a2l.parse_wlist(m.group(4))))
    return ops


def build(vals, lo, n):
    """Pruned trie over indices [lo, lo + n), n a power of two: ('L', v) when every
    value in the block is v (a missing index counts as 0), else ('N', left, right)."""
    if n == 1:
        return ('L', vals.get(lo, 0))
    h = n // 2
    l = build(vals, lo, h)
    r = build(vals, lo + h, h)
    if l[0] == 'L' and r[0] == 'L' and l[1] == r[1]:
        return l
    return ('N', l, r)


def get(t, d, i):
    """Mirror of AcirLean.Trie.get."""
    if t[0] == 'L':
        return t[1]
    if d == 0:
        return 0
    return get(t[2] if (i >> (d - 1)) & 1 else t[1], d - 1, i)


def nodes(t):
    return 1 if t[0] == 'L' else 1 + nodes(t[1]) + nodes(t[2])


def term(t):
    """Lean term, constructors written in full (no dot notation)."""
    if t[0] == 'L':
        return f'(Trie.leaf {t[1]})'
    return f'(Trie.node {term(t[1])} {term(t[2])})'


def top_term(t, level, s, k, defs):
    """The top `s` levels in full; each non-leaf subtree at level `s` becomes a definition."""
    if t[0] == 'L':
        return f'(Trie.leaf {t[1]})'
    if level == s:
        name = f'wt{k}'
        defs.append((name, term(t)))
        return name
    return (f'(Trie.node {top_term(t[1], level + 1, s, 2 * k, defs)} '
            f'{top_term(t[2], level + 1, s, 2 * k + 1, defs)})')


def main():
    args = sys.argv[1:]
    lean = None
    split = 12
    values = []
    if '--lean' in args:
        k = args.index('--lean')
        lean = (args[k + 1], args[k + 2])
        del args[k:k + 3]
    if '--split-depth' in args:
        k = args.index('--split-depth')
        split = int(args[k + 1])
        del args[k:k + 2]
    if '--values' in args:
        k = args.index('--values')
        values = [int(x) for x in args[k + 1].split(',')]
        del args[k:k + 2]
    txt, art, wit = args
    w = decode_witness(wit)
    ops = parse_ops(txt)
    fail = {'assert': 0, 'range': 0}
    missing = 0
    checked = {'assert': 0, 'range': 0, 'brillig': 0}
    for op in ops:
        if op[0] == 'assert':
            _, lhs, mul, lin, const = op
            ws = ([lhs] if lhs is not None else []) + [x for t in mul for x in t[1:]] + [t[1] for t in lin]
            if any(x not in w for x in ws):
                missing += 1
                continue
            val = (w[lhs] if lhs is not None else 0) - (sum(c * w[i] * w[j] for c, i, j in mul) + sum(c * w[i] for c, i in lin) + const)
            if val % P != 0:
                fail['assert'] += 1
            checked['assert'] += 1
        elif op[0] == 'range':
            if op[1] not in w:
                missing += 1
                continue
            if not w[op[1]] < 2 ** op[2]:
                fail['range'] += 1
            checked['range'] += 1
        else:
            checked['brillig'] += 1
    abi = json.load(open(art))['abi']
    report = {
        'witness_sha256': hashlib.sha256(open(wit, 'rb').read()).hexdigest(),
        'witness_entries': len(w),
        'max_index': max(w),
        'checked': checked,
        'failures': fail,
        'missing_witness_refs': missing,
        'public_values': {str(i): w.get(i) for i in range(6)},
        'values': {str(i): w.get(i) for i in values},
    }
    print(json.dumps(report, indent=1))
    if lean:
        out, ns = lean
        size = 1
        while size <= max(w):
            size *= 2
        depth = size.bit_length() - 1
        t = build(w, 0, size)
        bad = [i for i in range(size) if get(t, depth, i) != w.get(i, 0)]
        if bad:
            sys.exit(f"pruned trie lookup disagrees with the witness at {bad[:5]}")
        s_levels = max(0, depth - split)
        defs = []
        top = top_term(t, 0, s_levels, 0, defs)
        L = ['import AcirLean.Witness', '', '/-! Generated by scripts/witness_check.py. Do not edit.',
             f'Witness sha256 (gz file): {report["witness_sha256"]}',
             f'Pruned trie of depth {depth}: a block whose values are all equal (a missing index counts',
             'as 0) is one `Trie.leaf`, and `Trie.get` of a leaf gives its value at every index below it.',
             f'{nodes(t)} nodes; the extractor checked every lookup in [0, 2^{depth}) against the witness.',
             f'Subtrees of depth {split} are separate definitions ({len(defs)} of them). -/', '',
             'set_option maxRecDepth 65536', '', f'namespace AcirLean.{ns}', '', 'open AcirLean', '',
             f'def witnessDepth : Nat := {depth}', '']
        for name, body in defs:
            L += [f'noncomputable def {name} : Trie :=', f'  {body}', '']
        L += ['noncomputable def witnessTrie : Trie :=', f'  {top}', '', f'end AcirLean.{ns}', '']
        text = '\n'.join(L)
        open(out, 'w').write(text)
        print(json.dumps({'trie_depth': depth, 'trie_nodes': nodes(t), 'subtree_defs': len(defs),
                          'lookups_checked': size, 'lean_sha256': hashlib.sha256(text.encode()).hexdigest(),
                          'lean_bytes': len(text.encode())}), file=sys.stderr)
    sys.exit(1 if (fail['assert'] or fail['range'] or missing) else 0)


if __name__ == '__main__':
    main()
