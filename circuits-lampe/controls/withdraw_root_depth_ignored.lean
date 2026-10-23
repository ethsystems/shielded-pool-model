import Withdraw.Root

namespace Controls.Merkle
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Merkle.Fold Withdraw.Root
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_root_depth_ignored {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    proof_length ≤ 32 ∧
      commitment_root = merkleRoot hash2v
        (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) 32 indices path ∧
      nullifier = hash2v (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) spending_key := by
  obtain ⟨hn, hle, st₅, hroot⟩ := Withdraw.Nullifier.accepting_main_withdraw_rules nullifier token amount
    recipient commitment_root spending_key salt proof_length path indices accepts rejects_failure
  obtain ⟨st', st₆, heq⟩ := bmr_pinned_w _ _ _ _ hroot
  exact ⟨hle, (Prod.mk.inj (Option.some.inj heq)).2.symm, hn⟩

#print axioms withdraw_root_depth_ignored
end Controls.Merkle
