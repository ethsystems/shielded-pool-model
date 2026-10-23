import Transfer.Rules

namespace Controls.Transfer
open Lampe Deposit.Rules Determinism Transfer.HashGood Transfer.CastSteps Transfer.Forward Transfer.Rules

variable (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
  spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
  token_out_1 owner_out_1 salt_out_1 : Fp p)
variable (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
variable (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32)

theorem transfer_input1_owner_from_salt {st Q}
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
      (Deposit.Commitment.ownerKey salt_in_1) salt_in_1) spending_key ∧
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

#print axioms transfer_input1_owner_from_salt
end Controls.Transfer
