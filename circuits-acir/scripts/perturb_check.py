#!/usr/bin/env python3
"""Negative control for witness_check: change one witness value and list the failing opcodes.

usage: perturb_check.py <print-acir.txt> <witness.gz> <index> <new value> [<opcode index that must fail>]

Prints the number of failing ASSERT and RANGE opcodes and the first failing opcode indices.
With a required opcode index, exits 1 unless that opcode is among the failures.
"""
import importlib.util
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('wc', os.path.join(here, 'witness_check.py'))
wc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wc)
txt, wit, idx, val = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
must = int(sys.argv[5]) if len(sys.argv) > 5 else None
w = wc.decode_witness(wit)
w[idx] = val % wc.P
fa = fr = 0
failing = []
for k, op in enumerate(wc.parse_ops(txt)):
    if op[0] == 'assert':
        _, lhs, mul, lin, const = op
        v = (w[lhs] if lhs is not None else 0) - (
            sum(c * w[i] * w[j] for c, i, j in mul) + sum(c * w[i] for c, i in lin) + const)
        if v % wc.P != 0:
            fa += 1
            failing.append(k)
    elif op[0] == 'range':
        if not w[op[1]] < 2 ** op[2]:
            fr += 1
            failing.append(k)
res = {'mutation': f'w{idx}={val}', 'failing_assert': fa, 'failing_range': fr,
       'first_failing_opcodes': failing[:12], 'required_opcode': must,
       'required_fails': (must in failing) if must is not None else None}
print(json.dumps(res))
sys.exit(0 if (must is None or must in failing) else 1)
