import Withdraw.Nullifier

namespace Controls.Withdraw
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Withdraw.Nullifier

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_nullifier_args_swapped {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    nullifier = hash2v spending_key (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) ∧
      proof_length ≤ 32 ∧
      ∃ st₅, Omni p Γw st₅
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt,
            proof_length, indices, path])
        (fun r => ∃ st₆, r = some (st₆, commitment_root)) := by
  obtain ⟨st₄, hle, hroot, hv⟩ := accepting_main_rules_eq nullifier token amount recipient
    commitment_root spending_key salt proof_length path indices accepts rejects_failure
  obtain ⟨r, hr, -⟩ := (wgood_vmp bn254_gt _ _ _ _ _).inter st₄ _ _ hv hv
  obtain ⟨st₇, u, -, h7⟩ := hr
  obtain ⟨_, st₈, heq⟩ := poseidon2_pinned _ _ h7
  exact ⟨(Prod.mk.inj (Option.some.inj heq)).2.symm, hle, hroot⟩

#print axioms withdraw_nullifier_args_swapped
end Controls.Withdraw
