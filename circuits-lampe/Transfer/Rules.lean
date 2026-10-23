import Transfer.Forward
import Transfer.CastSteps

/-!
Transfer rules T2, T3, T4 and T10 over the complete extracted transfer `main`, on the patched
Lampe (with the pinned cast builtin), as plain equations over the pure forward functions of
`Deposit.Commitment` and `Poseidon.Hash2`: `ownerKey` (hash_1), `hash4` (hash_4) and `hash2v` (hash_2).
The note amounts are `u128`; the extracted `amount as Field` cast returns `amount.toNat`
(`Transfer.CastSteps.cast_u128_field`). The Merkle root stays relational: the extracted
`binary_merkle_root<32>` call on the plain commitment returns the public root.
-/

namespace Transfer.Rules
open Lampe Deposit.Rules Determinism Transfer.HashGood Transfer.CastSteps Transfer.Forward

/-- The Merkle part of `verify_merkle_proof<32>` in the transfer environment. -/
theorem vmp_rel_t {st Q} (leaf root : Fp p) (proof_length : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32)
    (hv : Omni p Γt st («transfer-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, root, proof_length, indices, path]) Q) (hvn : ¬ Q none) :
    proof_length ≤ 32 ∧ ∃ st₅, Omni p Γt st₅
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          leaf, proof_length, indices, path])
      (fun r => ∃ st₆, r = some (st₆, root)) := by
  have hv0 := step_call (decl := «transfer-0.0.0::verify_merkle_proof») (generics := h![(32 : U 32)])
    Transfer.Lookup.vmp_unique hv
  dsimp only [«transfer-0.0.0::verify_merkle_proof»] at hv0
  have hv1 := step_constU hv0
  obtain ⟨hle, hv2⟩ := step_assert (step_uLeq hv1 hvn) hvn
  simp only [decide_eq_true_eq] at hle
  refine ⟨hle, ?_⟩
  refine ⟨st, Omni.consequence (step_seq (step_fn (step_fn hv2)) hvn) ?_⟩
  rintro r ⟨st₅, root', rfl, hv3⟩
  obtain ⟨hr, _⟩ := step_assert (step_fEq hv3 hvn) hvn
  simp only [decide_eq_true_eq] at hr
  subst hr
  exact ⟨st₅, rfl⟩

/-- A `verify_merkle_proof<32>` call in an accepting `let`: its Merkle facts, and the
continuation runs. -/
theorem vmp_step {st tp'} {leaf root : Fp p} {proof_length : U 32}
    {indices : List.Vector Bool 32} {path : List.Vector (Fp p) 32}
    {b : Tp.denote p .unit → Expr (Tp.denote p) tp'} {Q : Option (State p × Tp.denote p tp') → Prop}
    (h : Omni p Γt st (.letIn («transfer-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, root, proof_length, indices, path]) b) Q) (hn : ¬ Q none) :
    (proof_length ≤ 32 ∧ ∃ st₅, Omni p Γt st₅
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          leaf, proof_length, indices, path])
      (fun r => ∃ st₆, r = some (st₆, root))) ∧ ∃ st', Omni p Γt st' (b ()) Q := by
  obtain ⟨Q₁, hv, hvn, st', u, -, hb⟩ := good_letIn (tgood_vmp Withdraw.Rules.bn254_gt _ _ _ _ _) h hn
  exact ⟨vmp_rel_t leaf root proof_length indices path hv hvn, st', hb⟩

variable (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
  spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
  token_out_1 owner_out_1 salt_out_1 : Fp p)
variable (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
variable (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32)

/-- T2, T3, T4 and T10 on the complete extracted transfer `main`. In every accepting execution,
with the input commitments `Cᵢ = hash4 token_in_i amount_in_i (ownerKey spending_key) salt_in_i`
(T2: both use the owner key of the one private `spending_key`):
* T3, input 0: `proof_length_0 ≤ 32` and the extracted `binary_merkle_root(hash_2, C₀, ...)`
  returns `commitment_root` (for every amount, zero included);
* T3, input 1: the same for `C₁` when `amount_in_1 ≠ 0`; for `amount_in_1 = 0` (the ballast
  note) the extracted `if` skips `verify_merkle_proof`, and nothing is claimed;
* T4: `nullifier_i = hash2v Cᵢ spending_key` for both inputs (ballast included);
* T10: `commitment_out_j = hash4 token_out_j amount_out_j owner_out_j salt_out_j`. -/
theorem accepting_main_transfer_rules {st Q}
    (accepts : Omni p Γt st
      («transfer-0.0.0::main».call h![]
        h![nullifier_0, nullifier_1, commitment_out_0, commitment_out_1, commitment_root,
          payload_hash, spending_key, token_in_0, amount_in_0, salt_in_0, token_in_1, amount_in_1,
          salt_in_1, token_out_0, amount_out_0, owner_out_0, salt_out_0, token_out_1, amount_out_1,
          owner_out_1, salt_out_1, proof_length_0, path_0, indices_0, proof_length_1, path_1,
          indices_1]) Q)
    (rejects_failure : ¬ Q none) :
    (proof_length_0 ≤ 32 ∧ ∃ st₀, Omni p Γt st₀
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
            (Deposit.Commitment.ownerKey spending_key) salt_in_0,
          proof_length_0, indices_0, path_0])
      (fun r => ∃ st', r = some (st', commitment_root))) ∧
    (amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧ ∃ st₁, Omni p Γt st₁
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
            (Deposit.Commitment.ownerKey spending_key) salt_in_1,
          proof_length_1, indices_1, path_1])
      (fun r => ∃ st', r = some (st', commitment_root))) ∧
    nullifier_0 = Poseidon.Hash2.hash2v (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_0) spending_key ∧
    nullifier_1 = Poseidon.Hash2.hash2v (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_1) spending_key ∧
    commitment_out_0 = Deposit.Commitment.hash4 token_out_0 ((amount_out_0.toNat : ℕ) : Fp p) owner_out_0 salt_out_0 ∧
    commitment_out_1 = Deposit.Commitment.hash4 token_out_1 ((amount_out_1.toNat : ℕ) : Fp p) owner_out_1 salt_out_1 := by
  have rf := rejects_failure
  have h0 := step_call Transfer.Lookup.main_unique accepts
  -- owner_pubkey = poseidon1(spending_key)
  obtain ⟨s1, h1⟩ := pin_letIn (tgood_poseidon1 Withdraw.Rules.bn254_gt _) (poseidon1_fwd _ _) (step_fn h0) rf
  -- commitment_in_0 = poseidon4(token_in_0, amount_in_0 as Field, owner_pubkey, salt_in_0)
  obtain ⟨s2, h2⟩ := pin_letIn (tgood_poseidon4 Withdraw.Rules.bn254_gt _ _ _ _) (poseidon4_fwd _ _ _ _ _)
    (step_cast_u128 (step_fn h1)) rf
  -- verify_merkle_proof(commitment_in_0, ...)
  obtain ⟨hT3a, s3, h3⟩ := vmp_step (step_fn h2) rf
  -- nullifier_0 == poseidon2(commitment_in_0, spending_key)
  obtain ⟨s4, h4⟩ := pin_letIn (tgood_poseidon2 Withdraw.Rules.bn254_gt _ _) (poseidon2_fwd _ _ _) (step_fn h3) rf
  obtain ⟨hn0, h5⟩ := step_assert (step_fEq h4 rf) rf
  simp only [decide_eq_true_eq] at hn0
  -- is_zero_note, commitment_in_1
  have h6 := step_uEq (step_litU h5) rf
  obtain ⟨s5, h7⟩ := pin_letIn (tgood_poseidon4 Withdraw.Rules.bn254_gt _ _ _ _) (poseidon4_fwd _ _ _ _ _)
    (step_cast_u128 (step_fn h6)) rf
  -- if !is_zero_note { verify_merkle_proof(commitment_in_1, ...) }
  have h8 := step_bNot h7 rf
  obtain ⟨Qi, hi, hin, hk⟩ := letIn_inv h8 rf
  have hz0 : BitVec.ofInt 128 0 = (0 : U 128) := by decide
  rw [hz0] at hi
  have hT3b : amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧ ∃ st₁, Omni p Γt st₁
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
            (Deposit.Commitment.ownerKey spending_key) salt_in_1,
          proof_length_1, indices_1, path_1])
      (fun r => ∃ st', r = some (st', commitment_root)) := by
    intro hne
    have hc : (!decide (amount_in_1 = 0)) = true := by rw [decide_eq_false hne]; rfl
    rw [hc] at hi
    exact (vmp_step (step_fn (ite_true_inv hi)) hin).1
  have hout : ∃ st', Qi (some (st', ())) := by
    by_cases hz : amount_in_1 = 0
    · have hc : (!decide (amount_in_1 = 0)) = false := by simp [hz]
      rw [hc] at hi
      cases ite_false_inv hi with | skip hq => exact ⟨_, hq⟩
    · have hc : (!decide (amount_in_1 = 0)) = true := by rw [decide_eq_false hz]; rfl
      rw [hc] at hi
      obtain ⟨-, st', hs⟩ := vmp_step (step_fn (ite_true_inv hi)) hin
      cases hs with | skip hq => exact ⟨_, hq⟩
  obtain ⟨s6, hq6⟩ := hout
  have h9 := hk () s6 hq6
  -- nullifier_1 == poseidon2(commitment_in_1, spending_key)
  obtain ⟨s7, h10⟩ := pin_letIn (tgood_poseidon2 Withdraw.Rules.bn254_gt _ _) (poseidon2_fwd _ _ _) (step_fn h9) rf
  obtain ⟨hn1, h11⟩ := step_assert (step_fEq h10 rf) rf
  simp only [decide_eq_true_eq] at hn1
  -- commitment_out_0 == poseidon4(token_out_0, amount_out_0 as Field, owner_out_0, salt_out_0)
  obtain ⟨s8, h12⟩ := pin_letIn (tgood_poseidon4 Withdraw.Rules.bn254_gt _ _ _ _) (poseidon4_fwd _ _ _ _ _)
    (step_cast_u128 (step_fn h11)) rf
  obtain ⟨hc0, h13⟩ := step_assert (step_fEq h12 rf) rf
  simp only [decide_eq_true_eq] at hc0
  -- commitment_out_1 == poseidon4(token_out_1, amount_out_1 as Field, owner_out_1, salt_out_1)
  obtain ⟨s9, h14⟩ := pin_letIn (tgood_poseidon4 Withdraw.Rules.bn254_gt _ _ _ _) (poseidon4_fwd _ _ _ _ _)
    (step_cast_u128 (step_fn h13)) rf
  obtain ⟨hc1, -⟩ := step_assert (step_fEq h14 rf) rf
  simp only [decide_eq_true_eq] at hc1
  exact ⟨hT3a, hT3b, hn0, hn1, hc0, hc1⟩

#print axioms vmp_rel_t
#print axioms vmp_step
#print axioms accepting_main_transfer_rules
end Transfer.Rules
