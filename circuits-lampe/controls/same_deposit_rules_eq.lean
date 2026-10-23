import Deposit.Commitment

namespace Controls.DepositHash
open Lampe Determinism Deposit.Commitment

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem same_deposit_rules_eq {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt ∧ proof_length ≤ 20 ∧
      ∃ st₄, Omni p Γ st₄
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            hash4 (ownerKey spending_key) attester ((issued_at.toNat : ℕ) : Fp p)
              ((expires_at.toNat : ℕ) : Fp p), proof_length, indices, path])
        (fun r => ∃ st₅, r = some (st₅, attestation_root)) := by
  obtain ⟨st₁, h⟩ := Deposit.PinnedCast.accepting_main_rules_pinned commitment token amount
    funding_address attestation_root payload_hash spending_key salt attester issued_at expires_at
    proof_length path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₃, heq3, h3⟩ := poseidon4_pinned _ _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq3)
  obtain ⟨_, st₄, leaf, heq4, hle, h4⟩ := poseidon4_pinned _ _ _ _ h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq4)
  exact ⟨rfl, hle, _, h4⟩

#print axioms same_deposit_rules_eq
end Controls.DepositHash
