#!/usr/bin/env python3
"""Write the chunked non-vacuity modules for one circuit.

usage: gen_nv.py <lean project dir> <Namespace> <Data.lean.json> <group size> <values statement>

Writes AcirLean/<NS>/NV/G<g>.lean: one `decide +kernel` theorem per chunk (`nv_chunk<k>`),
`group size` chunks per module, each group inside one part module (it imports only that
part and `Solved`). Writes AcirLean/<NS>/NonVacuity.lean: a term proof that combines the
chunk results along the right-nested `opcodes` of the parts mode, then `solved_satisfies`,
`satisfiable`, and `solved_values` (the given statement about `solved`, by `decide +kernel`).
Prints the group modules in build order, one per line.
"""
import json
import os
import sys


def main():
    if len(sys.argv) != 6:
        sys.exit(__doc__)
    d, ns, meta_path, g, values = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
    meta = json.load(open(meta_path))
    n = meta['chunks']
    part_of = {int(k): v for k, v in meta['part_of_chunk'].items()}
    if meta['parts'] <= 0:
        sys.exit("gen_nv.py expects a parts-mode Data.lean.json")
    groups = []
    cur = []
    for k in range(n):
        if cur and (len(cur) == g or part_of[cur[0]] != part_of[k]):
            groups.append(cur)
            cur = []
        cur.append(k)
    groups.append(cur)
    os.makedirs(f'{d}/AcirLean/{ns}/NV', exist_ok=True)
    mods = []
    for gi, ks in enumerate(groups):
        L = [f'import AcirLean.{ns}.Data.Part{part_of[ks[0]]}', f'import AcirLean.{ns}.Solved', '',
             f'namespace AcirLean.{ns}', '', 'open AcirLean', '']
        for k in ks:
            L += [f'theorem nv_chunk{k} : chunk{k}.all (fun op => op.check solved) = true := by',
                  '  decide +kernel', '']
        L += [f'end AcirLean.{ns}', '']
        open(f'{d}/AcirLean/{ns}/NV/G{gi}.lean', 'w').write('\n'.join(L))
        mods.append(f'AcirLean.{ns}.NV.G{gi}')
    chunks_expr = ' ++ ('.join(f'chunk{k}' for k in range(n)) + ')' * (n - 1)
    proof = ''
    for k in range(n - 1):
        proof += f'all_app nv_chunk{k} ('
    proof += f'nv_chunk{n - 1}' + ')' * (n - 1)
    L = [f'import AcirLean.{ns}.Data'] + [f'import {m}' for m in mods]
    L += ['', '/-!', f'# {ns}: the solved witness of `nargo execute` satisfies every opcode', '',
          'Each chunk is checked by the kernel (`decide +kernel`) in the `NV` modules; this module',
          'combines the chunk results with a term proof. It shows that `circuit.Satisfied` is not',
          'empty, and it checks the extractor and the semantics against the beta.21 solver on one',
          'input.', '-/', '', f'namespace AcirLean.{ns}', '', 'open AcirLean', '',
          'theorem all_app {l₁ l₂ : List Opcode} {p : Opcode → Bool}',
          '    (h₁ : l₁.all p = true) (h₂ : l₂.all p = true) : (l₁ ++ l₂).all p = true := by',
          '  rw [List.all_append, h₁, h₂]; rfl', '',
          'theorem solved_checks_chunks :',
          f'    ({chunks_expr}).all (fun op => op.check solved) = true :=',
          f'  {proof}', '',
          'theorem solved_checks : circuit.opcodes.all (fun op => op.check solved) = true :=',
          '  solved_checks_chunks', '',
          'theorem solved_satisfies : circuit.Satisfied solved :=',
          '  Circuit.satisfied_of_all solved_checks', '',
          f'theorem solved_values : {values} := by', '  decide +kernel', '',
          'theorem satisfiable : ∃ w, circuit.Satisfied w :=',
          '  ⟨solved, solved_satisfies⟩', '', f'end AcirLean.{ns}', '']
    open(f'{d}/AcirLean/{ns}/NonVacuity.lean', 'w').write('\n'.join(L))
    print('\n'.join(mods))


if __name__ == '__main__':
    main()
