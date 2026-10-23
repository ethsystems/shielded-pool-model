#!/usr/bin/env python3
"""Generate the must-fail controls (and their must-pass copies) into a directory.

  gen-controls.py OUT_DIR   write every control to OUT_DIR and print one line per control:
                            <name> <pass|fail>

Each generated control copies one theorem of the package (its statement and its proof) into a
new file, changes the statement only, and must fail to compile. The `same_*` copies change
nothing and must compile; `pass_*` controls change the statement and must compile too (the
patched cast builtin makes the changed statement true). The hand-written controls in
controls/hand/ are copied as they are and must fail. scripts/check.sh compares the output with
the committed controls/ files and compiles each one.
"""
import re
import shutil
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
SO = 'set_option backward.isDefEq.respectTransparency false'


def var_lines(s):
    return '\n'.join(l for l in s.splitlines() if l.startswith('variable '))


def var_blocks(s, skip_prime=False):
    lines, vb, i = s.splitlines(), [], 0
    while i < len(lines):
        if skip_prime and lines[i] == 'variable {p : Prime}':
            i += 1
        elif lines[i].startswith('variable '):
            vb.append(lines[i]); i += 1
            while i < len(lines) and lines[i].startswith('  '):
                vb.append(lines[i]); i += 1
        else:
            i += 1
    return '\n'.join(vb)


def cut_marker(s, start, marker):
    t = s[start:s.index(marker, start + 1)].rstrip() + '\n'
    k = t.index(':= by')
    return t[:k], t[k:]


def cut_next(s, start, extra=False):
    marks = ['\n/--', '\n#print', '\ntheorem']
    if extra:
        marks += ['\n/-!', '\nsection', '\nend']
    end = min(i for i in (s.find(m, start + (1 if m == '\ntheorem' else 0)) for m in marks) if i > 0)
    t = s[start:end].rstrip() + '\n'
    m = re.search(r':=( by)?\n', t)
    return t[:m.start()], t[m.start():]


# (namespace, module, theorem, header, variables, cut, {control: [(old, new), ...]})
SPEC = []


def group(ns, items):
    for it in items:
        SPEC.append((ns,) + it)


group('Controls.DepositRules', [
  ('Deposit.Rules', 'accepting_main_commitment', 'open Lampe Deposit.Rules', 'lines',
   ('marker', '#print axioms accepting_main_commitment'), {
    'same_deposit_commitment_rel': [],
    'deposit_commitment_rel_owner_from_salt': [('h![(⟨[spending_key], rfl⟩ : List.Vector (Fp p) 1)]',
                            'h![(⟨[salt], rfl⟩ : List.Vector (Fp p) 1)]')],
    'deposit_commitment_rel_token_amount_swapped': [('h![token, amount, owner, salt]', 'h![amount, token, owner, salt]')],
    'deposit_commitment_rel_owner_salt_swapped': [('h![token, amount, owner, salt]', 'h![token, amount, salt, owner]')],
  }),
  ('Deposit.Attestation', 'accepting_main_rules', 'open Lampe Deposit.Rules', 'lines',
   ('marker', '/-- Rules 2 and 4:'), {
    'same_deposit_attestation_rel': [],
    'deposit_attestation_rel_depth_strict': [('proof_length ≤ 20 ∧', 'proof_length < 20 ∧')],
    'deposit_attestation_rel_leaf_args_swapped': [('h![owner, attester, @Builtin', 'h![attester, owner, @Builtin')],
    'deposit_attestation_rel_root_is_commitment': [('r = some (st₅, attestation_root)', 'r = some (st₅, commitment)')],
    'pass_deposit_attestation_rel_canonical_casts': [('@Builtin.CastTp.cast _ _ c₁ p issued_at', '((issued_at.toNat : ℕ) : Fp p)'),
                         ('@Builtin.CastTp.cast _ _ c₂ p expires_at', '((expires_at.toNat : ℕ) : Fp p)')],
  }),
])
group('Controls.DepositCast', [
  ('Deposit.PinnedCast', 'accepting_main_rules_pinned', 'open Lampe Deposit.Rules Deposit.PinnedCast', 'lines-before',
   ('marker', '#print axioms cast_det'), {
    'same_deposit_pinned_rules': [],
    'deposit_pinned_rules_timestamps_swapped': [('((issued_at.toNat : ℕ) : Fp p), ((expires_at.toNat : ℕ) : Fp p)',
                               '((expires_at.toNat : ℕ) : Fp p), ((issued_at.toNat : ℕ) : Fp p)')],
  }),
  ('Deposit.PinnedCast', 'cast_u64_field', 'open Lampe Deposit.Rules Deposit.PinnedCast', 'lines-before',
   ('marker', 'theorem cast_not_unconstrained'), {
    'same_cast_u64_field': [],
    'cast_u64_field_plus_one': [('Q (some (st, ((v.toNat : ℕ) : Fp p)))', 'Q (some (st, ((v.toNat + 1 : ℕ) : Fp p)))')],
  }),
])
group('Controls.DepositHash', [
  ('Deposit.Commitment', 'accepting_main_commitment_eq', 'open Lampe Determinism Deposit.Commitment', 'lines', ('next',), {
    'same_deposit_commitment_eq': [],
    'deposit_commitment_eq_token_amount_swapped': [('commitment = hash4 token amount (ownerKey spending_key) salt',
                                       'commitment = hash4 amount token (ownerKey spending_key) salt')],
  }),
  ('Deposit.Commitment', 'accepting_main_rules_eq', 'open Lampe Determinism Deposit.Commitment', 'lines', ('next',), {
    'same_deposit_rules_eq': [],
    'deposit_rules_eq_timestamps_swapped': [('attester ((issued_at.toNat : ℕ) : Fp p)\n              ((expires_at.toNat : ℕ) : Fp p)',
                                        'attester ((expires_at.toNat : ℕ) : Fp p)\n              ((issued_at.toNat : ℕ) : Fp p)')],
    'deposit_rules_eq_depth_strict': [('salt ∧ proof_length ≤ 20 ∧', 'salt ∧ proof_length < 20 ∧')],
  }),
  ('Deposit.Commitment', 'accepting_main_owner_key', 'open Lampe Determinism Deposit.Commitment', 'lines', ('next',), {
    'same_deposit_owner_key': [],
    'deposit_owner_key_from_salt': [('h![token, amount, ownerKey spending_key, salt]', 'h![token, amount, ownerKey salt, salt]')],
  }),
  ('Deposit.Commitment', 'hash_1_pinned', 'open Lampe Determinism Deposit.Commitment', 'lines', ('next',), {
    'same_hash_1_pinned': [],
    'hash_1_pinned_plus_one': [("∃ st', Q (some (st', ownerKey sk))", "∃ st', Q (some (st', ownerKey (sk + 1)))")],
  }),
  ('Deposit.Commitment', 'poseidon4_pinned', 'open Lampe Determinism Deposit.Commitment', 'lines', ('next',), {
    'same_deposit_poseidon4_pinned': [],
    'deposit_poseidon4_pinned_swapped': [("∃ st', Q (some (st', hash4 a b c d))", "∃ st', Q (some (st', hash4 b a c d))")],
  }),
])
WZ = {'Withdraw.Rules': 'open Lampe Determinism Withdraw.HashGood Deposit.Rules Withdraw.Rules',
      'Withdraw.Nullifier': 'open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Withdraw.Nullifier',
      'Poseidon.Hash2': 'open Lampe Exec.Basic Exec.Heap Withdraw.HashGood Withdraw.Rules Poseidon.Hash2\n' + SO}
W3 = 'Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt'
group('Controls.Withdraw', [
  ('Withdraw.Rules', 'accepting_main_rel', WZ['Withdraw.Rules'], 'lines', ('next', True), {
    'same_withdraw_rel': [],
    'withdraw_rel_token_amount_swapped': [('h![token, amount, owner, salt]', 'h![amount, token, owner, salt]')],
    'withdraw_rel_nullifier_is_root': [('(fun r => ∃ st₈, r = some (st₈, nullifier))', '(fun r => ∃ st₈, r = some (st₈, commitment_root))')],
  }),
  ('Withdraw.Rules', 'accepting_main_rules_eq', WZ['Withdraw.Rules'], 'lines', ('next', True), {
    'same_withdraw_rules_eq': [],
    'withdraw_rules_eq_owner_from_salt': [(W3 + ',\n            proof_length',
                               'Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey salt) salt,\n            proof_length')],
    'withdraw_rules_eq_token_amount_swapped': [(W3 + ',\n            proof_length',
                                    'Deposit.Commitment.hash4 amount token (Deposit.Commitment.ownerKey spending_key) salt,\n            proof_length')],
  }),
  ('Withdraw.Nullifier', 'accepting_main_withdraw_rules', WZ['Withdraw.Nullifier'], 'lines', ('next', True), {
    'same_withdraw_rules': [],
    'withdraw_nullifier_key_is_salt': [(W3 + ') spending_key ∧', W3 + ') salt ∧')],
    'withdraw_nullifier_args_swapped': [('nullifier = hash2v (' + W3 + ') spending_key ∧',
                            'nullifier = hash2v spending_key (' + W3 + ') ∧')],
    'withdraw_depth_strict': [('proof_length ≤ 32 ∧', 'proof_length < 32 ∧')],
    'withdraw_root_is_nullifier': [('(fun r => ∃ st₆, r = some (st₆, commitment_root))', '(fun r => ∃ st₆, r = some (st₆, nullifier))')],
  }),
  ('Withdraw.Nullifier', 'poseidon2_pinned', WZ['Withdraw.Nullifier'], 'lines', ('next', True), {
    'same_withdraw_poseidon2_pinned': [],
    'withdraw_poseidon2_pinned_swapped': [("∃ st', Q (some (st', hash2v a b))", "∃ st', Q (some (st', hash2v b a))")],
  }),
  ('Poseidon.Hash2', 'hash_2_fwd', WZ['Poseidon.Hash2'], 'lines', ('next', True), {
    'same_hash_2_fwd': [],
    'hash_2_fwd_plus_one': [("(fun r => ∃ st', r = some (st', hash2v a b))", "(fun r => ∃ st', r = some (st', hash2v a (b + 1)))")],
  }),
])
TX = {'Transfer.Rules': 'open Lampe Deposit.Rules Determinism Transfer.HashGood Transfer.CastSteps Transfer.Forward Transfer.Rules',
      'Transfer.Relational': 'open Lampe Deposit.Rules Determinism Transfer.HashGood Transfer.CastSteps Transfer.Forward Transfer.Rules Transfer.Relational',
      'Transfer.CastSteps': 'open Lampe Deposit.Rules Determinism Transfer.CastSteps',
      'Transfer.Forward': 'open Lampe Determinism Transfer.HashGood Transfer.Forward',
      'Transfer.Execution': 'open Lampe Determinism Transfer.HashGood Transfer.Forward Transfer.Rules Transfer.Execution'}
OUT0 = 'commitment_out_0 = Deposit.Commitment.hash4 token_out_0 ((amount_out_0.toNat : ℕ) : Fp p) owner_out_0 salt_out_0 ∧'
group('Controls.Transfer', [
  ('Transfer.Relational', 'accepting_main_rel', TX['Transfer.Relational'], 'blocks', ('next', True), {
    'same_transfer_rel': [],
    'transfer_rel_input1_owner_is_key': [('h![token_in_1, ((amount_in_1.toNat : ℕ) : Fp p), owner, salt_in_1]',
                                       'h![token_in_1, ((amount_in_1.toNat : ℕ) : Fp p), spending_key, salt_in_1]')],
    'transfer_rel_ballast_unguarded': [('(amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧', '(proof_length_1 ≤ 32 ∧')],
    'transfer_rel_nullifier_args_swapped': [('h![c₀, spending_key]', 'h![spending_key, c₀]')],
    'transfer_rel_output_owner_salt_swapped': [('owner_out_0, salt_out_0]', 'salt_out_0, owner_out_0]')],
  }),
  ('Transfer.Rules', 'accepting_main_transfer_rules', TX['Transfer.Rules'], 'blocks', ('next', True), {
    'same_transfer_rules': [],
    'transfer_input1_owner_from_salt': [('(Deposit.Commitment.ownerKey spending_key) salt_in_1) spending_key ∧',
                                      '(Deposit.Commitment.ownerKey salt_in_1) salt_in_1) spending_key ∧')],
    'transfer_depth_strict': [('(proof_length_0 ≤ 32 ∧', '(proof_length_0 < 32 ∧')],
    'transfer_ballast_unguarded': [('(amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧', '(proof_length_1 ≤ 32 ∧')],
    'transfer_root_is_nullifier': [("proof_length_0, indices_0, path_0])\n      (fun r => ∃ st', r = some (st', commitment_root))",
                                 "proof_length_0, indices_0, path_0])\n      (fun r => ∃ st', r = some (st', nullifier_0))")],
    'transfer_nullifier_key_is_salt': [('(Deposit.Commitment.ownerKey spending_key) salt_in_0) spending_key ∧',
                           '(Deposit.Commitment.ownerKey spending_key) salt_in_0) salt_in_0 ∧')],
    'transfer_nullifiers_swapped': [('    nullifier_0 = Poseidon.Hash2.hash2v', '    NULLX = Poseidon.Hash2.hash2v'),
                                 ('    nullifier_1 = Poseidon.Hash2.hash2v', '    nullifier_0 = Poseidon.Hash2.hash2v'),
                                 ('    NULLX =', '    nullifier_1 =')],
    'transfer_output_token_amount_swapped': [(OUT0, 'commitment_out_0 = Deposit.Commitment.hash4 ((amount_out_0.toNat : ℕ) : Fp p) token_out_0 owner_out_0 salt_out_0 ∧')],
    'transfer_output1_owner_is_output0': [('((amount_out_1.toNat : ℕ) : Fp p) owner_out_1 salt_out_1', '((amount_out_1.toNat : ℕ) : Fp p) owner_out_0 salt_out_1')],
  }),
  ('Transfer.CastSteps', 'cast_u128_field', TX['Transfer.CastSteps'], 'blocks', ('next', True), {
    'same_cast_u128_field': [],
    'cast_u128_field_plus_one': [('Q (some (st, ((v.toNat : ℕ) : Fp p)))', 'Q (some (st, ((v.toNat + 1 : ℕ) : Fp p)))')],
  }),
  ('Transfer.Forward', 'poseidon4_pinned', TX['Transfer.Forward'], 'blocks', ('next', True), {
    'same_transfer_poseidon4_pinned': [],
    'transfer_poseidon4_pinned_swapped': [("∃ st', Q (some (st', Deposit.Commitment.hash4 a b c d))", "∃ st', Q (some (st', Deposit.Commitment.hash4 b a c d))")],
  }),
  ('Transfer.Execution', 'transfer_rules_nonvacuous', TX['Transfer.Execution'], 'blocks', ('next', True), {
    'same_transfer_nonvacuous': [],
    'transfer_nonvacuous_ballast_bound': [('¬ ((33 : U 32) ≤ 32)', '((33 : U 32) ≤ 32)')],
  }),
])
NH = {'Merkle.Fold': f'open Lampe Exec.Basic Exec.Heap Merkle.Fold\n{SO}',
      'Withdraw.Root': f'open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Merkle.Fold Withdraw.Root\nopen Exec.Basic\n{SO}',
      'Transfer.Root': 'open Lampe Determinism Transfer.HashGood Transfer.Forward Merkle.Fold Poseidon.Hash2 Transfer.Root',
      'Deposit.AttestationRoot': f'open Lampe Determinism Deposit.Commitment Poseidon.Hash2 Merkle.Fold Deposit.AttestationRoot\n{SO}'}
W2LEAF = '(Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) proof_length indices path ∧'
R4 = '((expires_at.toNat : ℕ) : Fp p)) proof_length indices path'
group('Controls.Merkle', [
  ('Merkle.Fold', 'bmr_fwd', NH['Merkle.Fold'], ('fixed', 'variable {p : Prime}'), ('next', True), {
    'same_bmr_fwd': [],
    'bmr_fwd_direction_flipped': [('merkleRoot h leaf depth indices path))', 'merkleRoot (fun a b => h b a) leaf depth indices path))')],
    'bmr_fwd_all_levels_active': [('merkleRoot h leaf depth indices path))', 'merkleRoot h leaf N indices path))')],
  }),
  ('Withdraw.Root', 'accepting_main_withdraw_root', NH['Withdraw.Root'], 'blocks-noprime', ('next', True), {
    'same_withdraw_root': [],
    'withdraw_root_depth_ignored': [(W2LEAF, W2LEAF.replace(') proof_length indices path', ') 32 indices path'))],
    'withdraw_root_leaf_is_nullifier': [(W2LEAF, 'nullifier proof_length indices path ∧')],
  }),
  ('Withdraw.Root', 'main_accepting_execution_depth', NH['Withdraw.Root'], 'blocks-noprime', ('next', True), {
    'same_withdraw_execution_depth': [],
    'withdraw_execution_root_is_leaf': [('merkleRoot hash2v Withdraw.Nullifier.C0 d indices path, (0 : Fp p)', 'Withdraw.Nullifier.C0, (0 : Fp p)')],
  }),
  ('Withdraw.Root', 'root_depth3', NH['Withdraw.Root'], 'blocks-noprime', ('next', True), {
    'same_root_depth3': [],
    'root_depth3_two_levels': [('hash2v (hash2v (hash2v Withdraw.Nullifier.C0 0) 0) 0', 'hash2v (hash2v Withdraw.Nullifier.C0 0) 0')],
  }),
  ('Transfer.Root', 'accepting_main_transfer_root', NH['Transfer.Root'], 'blocks-noprime', ('next', True), {
    'same_transfer_root': [],
    'transfer_root_input1_unguarded': [('(amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧', '(proof_length_1 ≤ 32 ∧')],
    'transfer_root_input0_path_of_input1': [('proof_length_0 indices_0 path_0', 'proof_length_0 indices_1 path_1')],
  }),
  ('Deposit.AttestationRoot', 'accepting_main_attestation_root', NH['Deposit.AttestationRoot'], 'blocks-noprime', ('next', True), {
    'same_attestation_root': [],
    'attestation_root_depth_ignored': [(R4, R4.replace('proof_length indices path', '20 indices path'))],
    'attestation_root_timestamps_swapped': [('attester ((issued_at.toNat : ℕ) : Fp p)\n          ((expires_at.toNat : ℕ) : Fp p))',
                                  'attester ((expires_at.toNat : ℕ) : Fp p)\n          ((issued_at.toNat : ℕ) : Fp p))')],
  }),
])
HAND = ['bdet_pure_on_fresh', 'config_det_without_certificate', 'to_le_bits_good_without_bound',
        'toLeBits_det_without_bound', 'cast_unconstrained']


def main():
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for ns, mod, thm, head, vmode, cut, controls in SPEC:
        s = (PKG / Path(*mod.split('.'))).with_suffix('.lean').read_text()
        start = s.index(f'theorem {thm} ' if cut[0] == 'next' else f'theorem {thm}')
        if vmode == 'lines':
            variables = var_lines(s)
        elif vmode == 'lines-before':
            vpos = s.find('\nvariable ')
            variables = var_lines(s) if 0 <= vpos < start else ''
        elif vmode == 'blocks':
            variables = var_blocks(s)
        elif vmode == 'blocks-noprime':
            variables = var_blocks(s, skip_prime=True)
        else:
            variables = vmode[1]
        stmt, proof = cut_marker(s, start, cut[1]) if cut[0] == 'marker' else cut_next(s, start, len(cut) > 1)
        for name, muts in controls.items():
            st2 = stmt
            for a, b in muts:
                assert st2.count(a) == 1, (name, a, st2.count(a))
                st2 = st2.replace(a, b)
            body = f'import {mod}\n\nnamespace {ns}\n{head}\n\n{variables}\n\n'
            body += st2.replace(f'theorem {thm}', f'theorem {name}', 1) + proof
            body += f'\n#print axioms {name}\nend {ns}\n'
            (out / f'{name}.lean').write_text(body)
            rows.append((name, 'pass' if name.startswith(('same_', 'pass_')) else 'fail'))
    for name in HAND:
        shutil.copy(PKG / 'controls' / 'hand' / f'{name}.lean', out / f'{name}.lean')
        rows.append((name, 'fail'))
    names = [r[0] for r in rows]
    assert len(set(names)) == len(names), 'duplicate control name'
    for name, verdict in rows:
        print(name, verdict)


if __name__ == '__main__':
    main()
