#!/usr/bin/env python3
"""Compare the artifact bytecode with the printed `func 0`, opcode by opcode.

usage: bytecode_check.py <print-acir.txt> <artifact.json>

Decodes the artifact's `bytecode` (base64, gzip, one format byte 3, then msgpack in the
compact form) with the msgpack reader of witness_check.py, and parses the print with the
acir2lean parser. Then it requires, for the one ACIR function: the same private, public
and return witness lists; the same number of opcodes; and at each index the same opcode
kind with the same content. RANGE: the same witness and bit count. ASSERT: the bytecode
expression equals the printed `lhs - rhs`, or its negation, as a polynomial over the BN254
scalar field (terms merged, `wi*wj` = `wj*wi`). BRILLIG CALL: the same function id and
outputs (the semantics reads nothing else). Prints a JSON report; exits 1 on any
difference.
"""
import base64
import gzip
import importlib.util
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('wc', os.path.join(here, 'witness_check.py'))
wc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wc)
a2l, P = wc.a2l, wc.P


def field(b):
    if not isinstance(b, bytes) or len(b) != 32:
        raise ValueError(f'field element is not 32 bytes: {b!r}')
    x = int.from_bytes(b, 'big')
    if x >= P:
        raise ValueError('non-canonical field element')
    return x


def poly(terms):
    """Merge (coefficient, key) pairs into {key: coefficient mod P}, dropping zeros."""
    out = {}
    for c, k in terms:
        out[k] = (out.get(k, 0) + c) % P
    return {k: c for k, c in out.items() if c}


def bytecode_op(op):
    if not isinstance(op, dict) or len(op) != 1:
        raise ValueError(f'bad opcode encoding {op!r}'[:200])
    kind, body = next(iter(op.items()))
    if kind == 'AssertZero':
        mul, lin, const = body
        return ('assert', poly([(field(c), ('m',) + tuple(sorted((i, j)))) for c, i, j in mul] +
                               [(field(c), ('l', i)) for c, i in lin] + [(field(const), ('c',))]))
    if kind == 'BlackBoxFuncCall' and list(body) == ['RANGE']:
        inp, bits = body['RANGE']
        if list(inp) != ['Witness']:
            raise ValueError(f'RANGE input is not a witness: {inp!r}')
        return ('range', inp['Witness'], bits)
    if kind == 'BrilligCall':
        fid, _inputs, outputs, _predicate = body
        outs = []
        for o in outputs:
            if list(o) != ['Simple']:
                raise ValueError(f'unsupported Brillig output {o!r}')
            outs.append(o['Simple'])
        return ('brillig', fid, outs)
    raise ValueError(f'unsupported opcode kind {kind}')


def printed_op(op):
    if op[0] == 'assert':
        _, lhs, mul, lin, const = op
        terms = [] if lhs is None else [(1, ('l', lhs))]
        terms += [(-c, ('m',) + tuple(sorted((i, j)))) for c, i, j in mul]
        terms += [(-c, ('l', i)) for c, i in lin] + [(-const, ('c',))]
        return ('assert', poly(terms))
    return op


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    txt, art = sys.argv[1], sys.argv[2]
    raw = gzip.decompress(base64.b64decode(json.load(open(art))['bytecode']))
    if raw[0] != 3:
        sys.exit(f'bytecode format byte {raw[0]} != 3 (msgpack-compact)')
    prog, end = wc.unpack(raw, 1)
    if end != len(raw):
        sys.exit('trailing bytes in the bytecode')
    functions, brillig = prog
    if len(functions) != 1:
        sys.exit(f'expected one ACIR function, found {len(functions)}')
    _name, _cwi, ops_b, priv_b, pub_b, ret_b, _messages = functions[0]
    lines = open(txt).read().split('\n')
    s = lines.index('func 0') + 1
    header = {}
    for l in lines[s:s + 3]:
        m = a2l.PARAMS_RE.match(l)
        header[m.group(1)] = a2l.parse_wlist(m.group(2))
    ops_p = wc.parse_ops(txt)
    params = {'private': priv_b == header['private parameters'],
              'public': pub_b == header['public parameters'],
              'return': ret_b == header['return values']}
    diffs, sign, counts = [], {'same': 0, 'negated': 0}, {'assert': 0, 'range': 0, 'brillig': 0}
    if len(ops_b) != len(ops_p):
        diffs.append(f'opcode count: bytecode {len(ops_b)}, print {len(ops_p)}')
    for k, (ob, op) in enumerate(zip(ops_b, ops_p)):
        b, p = bytecode_op(ob), printed_op(op)
        counts[b[0]] += 1
        if b[0] == 'assert' and p[0] == 'assert':
            if b[1] == p[1]:
                sign['same'] += 1
                continue
            if b[1] == {key: (P - c) % P for key, c in p[1].items()}:
                sign['negated'] += 1
                continue
        elif b == p:
            continue
        diffs.append(f'opcode {k}: bytecode {b!r}, print {p!r}'[:300])
    for kind, ok in params.items():
        if not ok:
            diffs.append(f'{kind} parameter lists differ')
    report = {'format_byte': raw[0], 'acir_functions': len(functions), 'brillig_functions': len(brillig),
              'opcodes': len(ops_b), 'counts': counts, 'assert_sign': sign, 'params_match': params,
              'differences': len(diffs), 'first_differences': diffs[:5]}
    print(json.dumps(report, indent=1))
    sys.exit(1 if diffs else 0)


if __name__ == '__main__':
    main()
