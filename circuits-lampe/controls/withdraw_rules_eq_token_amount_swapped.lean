import Withdraw.Rules

namespace Controls.Withdraw
open Lampe Determinism Withdraw.HashGood Deposit.Rules Withdraw.Rules

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_rules_eq_token_amount_swapped {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₄, proof_length ≤ 32 ∧
      (∃ st₅, Omni p Γw st₅
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            Deposit.Commitment.hash4 amount token (Deposit.Commitment.ownerKey spending_key) salt,
            proof_length, indices, path])
        (fun r => ∃ st₆, r = some (st₆, commitment_root))) ∧
      Omni p Γw st₄ («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
          h![Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt,
            commitment_root, proof_length, indices, path])
        (fun r => ∃ st₇ u, r = some (st₇, u) ∧
          Omni p Γw st₇ («withdraw-0.0.0::poseidon2».call h![] h![
              Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt, spending_key])
            (fun r => ∃ st₈, r = some (st₈, nullifier))) := by
  have h := accepting_main_rel nullifier token amount recipient commitment_root spending_key salt
    proof_length path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, st₃, h2⟩ := poseidon1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₄, cm, heq4, hle, hroot, hv⟩ := poseidon4_pinned _ _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq4)
  exact ⟨_, hle, hroot, hv⟩

#print axioms withdraw_rules_eq_token_amount_swapped
end Controls.Withdraw
