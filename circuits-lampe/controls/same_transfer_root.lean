import Transfer.Root

namespace Controls.Merkle
open Lampe Determinism Transfer.HashGood Transfer.Forward Merkle.Fold Poseidon.Hash2 Transfer.Root

variable (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
  spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
  token_out_1 owner_out_1 salt_out_1 : Fp p)
variable (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
variable (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32)

theorem same_transfer_root {st Q}
    (accepts : Omni p Γt st
      («transfer-0.0.0::main».call h![]
        h![nullifier_0, nullifier_1, commitment_out_0, commitment_out_1, commitment_root,
          payload_hash, spending_key, token_in_0, amount_in_0, salt_in_0, token_in_1, amount_in_1,
          salt_in_1, token_out_0, amount_out_0, owner_out_0, salt_out_0, token_out_1, amount_out_1,
          owner_out_1, salt_out_1, proof_length_0, path_0, indices_0, proof_length_1, path_1,
          indices_1]) Q)
    (rejects_failure : ¬ Q none) :
    (proof_length_0 ≤ 32 ∧ commitment_root = merkleRoot hash2v
      (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
        (Deposit.Commitment.ownerKey spending_key) salt_in_0) proof_length_0 indices_0 path_0) ∧
    (amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧ commitment_root = merkleRoot hash2v
      (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
        (Deposit.Commitment.ownerKey spending_key) salt_in_1) proof_length_1 indices_1 path_1) ∧
    nullifier_0 = hash2v (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_0) spending_key ∧
    nullifier_1 = hash2v (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_1) spending_key ∧
    commitment_out_0 = Deposit.Commitment.hash4 token_out_0 ((amount_out_0.toNat : ℕ) : Fp p) owner_out_0 salt_out_0 ∧
    commitment_out_1 = Deposit.Commitment.hash4 token_out_1 ((amount_out_1.toNat : ℕ) : Fp p) owner_out_1 salt_out_1 := by
  obtain ⟨⟨hle0, st₀, hr0⟩, h1, hn0, hn1, ho0, ho1⟩ := Transfer.Rules.accepting_main_transfer_rules
    nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
    spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
    token_out_1 owner_out_1 salt_out_1 amount_in_0 amount_in_1 amount_out_0 amount_out_1
    proof_length_0 proof_length_1 path_0 path_1 indices_0 indices_1 accepts rejects_failure
  refine ⟨⟨hle0, root_eq _ _ _ _ hr0⟩, ?_, hn0, hn1, ho0, ho1⟩
  intro hne
  obtain ⟨hle1, st₁, hr1⟩ := h1 hne
  exact ⟨hle1, root_eq _ _ _ _ hr1⟩

#print axioms same_transfer_root
end Controls.Merkle
