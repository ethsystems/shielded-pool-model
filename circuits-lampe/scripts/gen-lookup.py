#!/usr/bin/env python3
"""Regenerate the `UniqueDecl` lookup certificates from the base certificate leaves.

  gen-lookup.py OUT_DIR   write the six generated certificate modules (each an aggregate and
                          59 leaves) under OUT_DIR, at their paths in this package

A circuit environment `«c».env` is the concatenation of 59 module environments. Each leaf
proves, for one module environment and by `rfl`, which declarations of a given name it holds;
the aggregate concatenates the leaves (`simp only`) and derives `Deposit.Range.UniqueDecl`. The
59 module environments and their imports come from the leaves of `Deposit.MainLookup`, which are
written by hand. scripts/check.sh compares the output with the committed files.
"""
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
P = '«poseidon-0.0.0».Poseidon'
STD_FIELD = ('«std-1.0.0-beta.21».Field.Mod.env', '«std-1.0.0-beta.21».Extracted.Field.Mod')

# key: (declaration, declaring env, declaring import, copies of the declaring env in the circuit env)
SPECS = {
  'config': ('«poseidon-0.0.0::poseidon::config»', f'{P}.Mod.env', '«poseidon-0.0.0».Extracted.Poseidon.Mod', 1),
  'permute': ('«poseidon-0.0.0::poseidon::permute»', f'{P}.Mod.env', '«poseidon-0.0.0».Extracted.Poseidon.Mod', 1),
  'sigma': ('«poseidon-0.0.0::poseidon::sigma»', f'{P}.Mod.env', '«poseidon-0.0.0».Extracted.Poseidon.Mod', 1),
  'apply_matrix': ('«poseidon-0.0.0::poseidon::apply_matrix»', f'{P}.Mod.env', '«poseidon-0.0.0».Extracted.Poseidon.Mod', 1),
  'hash_1': ('«poseidon-0.0.0::poseidon::bn254::hash_1»', f'{P}.Bn254.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254', 1),
  'hash_2': ('«poseidon-0.0.0::poseidon::bn254::hash_2»', f'{P}.Bn254.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254', 1),
  'hash_4': ('«poseidon-0.0.0::poseidon::bn254::hash_4»', f'{P}.Bn254.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254', 1),
  'hash_internal': ('«poseidon-0.0.0::poseidon::bn254::hash_internal»', f'{P}.Bn254.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254', 1),
  'x5_2': ('«poseidon-0.0.0::poseidon::bn254::perm::x5_2»', f'{P}.Bn254.Perm.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm', 1),
  'x5_3': ('«poseidon-0.0.0::poseidon::bn254::perm::x5_3»', f'{P}.Bn254.Perm.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm', 1),
  'x5_5': ('«poseidon-0.0.0::poseidon::bn254::perm::x5_5»', f'{P}.Bn254.Perm.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm', 1),
  'x5_2_config': ('«poseidon-0.0.0::poseidon::bn254::consts::x5_2_config»', f'{P}.Bn254.Consts.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts', 1),
  'x5_3_config': ('«poseidon-0.0.0::poseidon::bn254::consts::x5_3_config»', f'{P}.Bn254.Consts.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts', 1),
  'x5_5_config': ('«poseidon-0.0.0::poseidon::bn254::consts::x5_5_config»', f'{P}.Bn254.Consts.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts', 1),
  'alpha': ('«poseidon-0.0.0::poseidon::bn254::consts::alpha»', f'{P}.Bn254.Consts.env', '«poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts', 1),
  'pow_32': ('«std-1.0.0-beta.21::field::pow_32»',) + STD_FIELD + (3,),
  'to_le_bits': ('«std-1.0.0-beta.21::field::to_le_bits»',) + STD_FIELD + (3,),
  'range': ('«std-1.0.0-beta.21::field::assert_max_bit_size»',) + STD_FIELD + (3,),
  'bmr': ('«binary_merkle_root-0.0.0::binary_merkle_root»', '«binary_merkle_root-0.0.0».Lib.env', '«binary_merkle_root-0.0.0».Extracted.Lib', 1),
}


def circuit_specs(c):
    m = (f'«{c}-0.0.0».Main.env', f'«{c}-0.0.0».Extracted.Main', 1)
    return {'main': (f'«{c}-0.0.0::main»',) + m, 'vmp': (f'«{c}-0.0.0::verify_merkle_proof»',) + m,
            'poseidon1': (f'«{c}-0.0.0::poseidon1»',) + m, 'poseidon2': (f'«{c}-0.0.0::poseidon2»',) + m,
            'poseidon4': (f'«{c}-0.0.0::poseidon4»',) + m}


HASH = 'hash_1 hash_4 hash_internal x5_2 x5_5 x5_2_config x5_5_config alpha permute sigma apply_matrix pow_32 to_le_bits poseidon4'
WIDE = ('config permute sigma apply_matrix hash_1 hash_2 hash_4 hash_internal x5_2 x5_3 x5_5 x5_2_config '
        'x5_3_config x5_5_config alpha pow_32 to_le_bits range bmr main vmp poseidon1 poseidon2 poseidon4')
# namespace, circuit, names
GROUPS = [
    ('Deposit.ConfigLookup', 'deposit', 'config'),
    ('Deposit.HashLookup', 'deposit', HASH),
    ('Deposit.MerkleLookup', 'deposit', 'hash_2 x5_3 x5_3_config bmr'),
    ('Withdraw.Lookup', 'withdraw', WIDE),
    ('Transfer.Lookup', 'transfer', WIDE.replace(' range', '')),
]


def base_leaves():
    for i in range(59):
        src = (PKG / 'Deposit' / 'MainLookup' / f'Leaf{i}.lean').read_text()
        imports = [l for l in src.splitlines() if l.startswith('import ')]
        env = re.search(r'theorem main_filter_%d : (\S+)\.functions\.filter' % i, src).group(1)
        yield i, imports, env


def gen_group(out, ns, circuit, names):
    names = names.split()
    specs = {**SPECS, **circuit_specs(circuit)}
    d = out / Path(*ns.split('.'))
    d.mkdir(parents=True, exist_ok=True)
    extra_imports = sorted({specs[n][2] for n in names})
    main_env, nmain = f'«{circuit}-0.0.0».Main.env', 0
    for i, imports, env in base_leaves():
        imports = [l.replace('«deposit-0.0.0».Extracted.Main', f'«{circuit}-0.0.0».Extracted.Main') for l in imports]
        if env == '«deposit-0.0.0».Main.env':
            env, nmain = main_env, nmain + 1
        imps = list(dict.fromkeys(imports + [f'import {m}' for m in extra_imports]))
        body = '\n'.join(imps) + f'\nopen Lampe\nnamespace {ns}\n'
        for n in names:
            decl, denv, _, _ = specs[n]
            rhs = f'[{decl}]' if env == denv else '[]'
            body += f'theorem {n}_filter_{i} : {env}.functions.filter (fun d => d.name == {decl}.name) = {rhs} := by rfl\n'
        body += f'end {ns}\n'
        if circuit != 'deposit':
            assert 'deposit' not in body
        (d / f'Leaf{i}.lean').write_text(body)
    assert nmain == 1
    agg = ''.join(f'import {ns}.Leaf{i}\n' for i in range(59))
    agg += f'import «{circuit}-0.0.0».Extracted\nimport Deposit.Range\nopen Lampe\nnamespace {ns}\n'
    for n in names:
        decl, _, _, k = specs[n]
        rhs = f'[{decl}]' if k == 1 else f'List.replicate {k} {decl}'
        leafs = ', '.join(f'{n}_filter_{i}' for i in range(59))
        agg += (f'theorem {n}_filter : «{circuit}-0.0.0».env.functions.filter (fun d => d.name == {decl}.name) = {rhs} := by\n'
                f'  simp only [«{circuit}-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, '
                f'Env.functions_append, List.filter_append, {leafs}, List.nil_append, List.append_nil]\n')
        if k != 1:
            agg += '  rfl\n'
        agg += (f'theorem {n}_unique : Deposit.Range.UniqueDecl «{circuit}-0.0.0».env {decl} :=\n'
                f'  Deposit.Range.unique_of_filter (n := {k}) {n}_filter\n')
        agg += f'#print axioms {n}_filter\n#print axioms {n}_unique\n'
    agg += f'end {ns}\n'
    (d.parent / f'{d.name}.lean').write_text(agg)


def gen_verify(out):
    ns = 'Deposit.VerifyLookup'
    decl = '«deposit-0.0.0::verify_merkle_proof»'
    d = out / 'Deposit' / 'VerifyLookup'
    d.mkdir(parents=True, exist_ok=True)
    names = []
    for i, imports, env in base_leaves():
        rhs = f'[{decl}]' if env == '«deposit-0.0.0».Main.env' else '[]'
        body = '\n'.join(imports) + f'\nopen Lampe\nnamespace {ns}\n'
        body += f'theorem verify_filter_{i} : {env}.functions.filter (fun d => d.name == {decl}.name) = {rhs} := by rfl\n'
        body += f'end {ns}\n'
        (d / f'Leaf{i}.lean').write_text(body)
        names.append(f'verify_filter_{i}')
    agg = ''.join(f'import {ns}.Leaf{i}\n' for i in range(59))
    agg += f'import «deposit-0.0.0».Extracted\nopen Lampe\nnamespace {ns}\n'
    agg += (f'theorem verify_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == {decl}.name) = [{decl}] := by\n'
            '  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, '
            'Env.functions_append, List.filter_append, ' + ', '.join(names) + ', List.nil_append, List.append_nil]\n')
    agg += f'#print axioms verify_filter\nend {ns}\n'
    (out / 'Deposit' / 'VerifyLookup.lean').write_text(agg)


def main():
    out = Path(sys.argv[1])
    gen_verify(out)
    for g in GROUPS:
        gen_group(out, *g)
    print(f'generated {1 + len(GROUPS)} certificate modules of 59 leaves each')


if __name__ == '__main__':
    main()
