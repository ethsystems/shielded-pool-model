import Deposit.Commitment

namespace Controls.DepositHash
open Lampe Determinism Deposit.Commitment

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem same_deposit_owner_key {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₂, Omni p Γ st₂
      («deposit-0.0.0::poseidon4».call h![] h![token, amount, ownerKey spending_key, salt])
      (fun r => ∃ st₃, r = some (st₃, commitment)) := by
  obtain ⟨st₁, h⟩ := Deposit.Rules.accepting_main_commitment commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length
    path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  exact ⟨_, h2⟩

#print axioms same_deposit_owner_key
end Controls.DepositHash
