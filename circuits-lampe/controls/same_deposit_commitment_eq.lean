import Deposit.Commitment

namespace Controls.DepositHash
open Lampe Determinism Deposit.Commitment

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem same_deposit_commitment_eq {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt := by
  obtain ⟨st₁, h⟩ := Deposit.Rules.accepting_main_commitment commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length
    path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₃, heq3⟩ := poseidon4_pinned _ _ _ _ h2
  exact (Prod.mk.inj (Option.some.inj heq3)).2.symm

#print axioms same_deposit_commitment_eq
end Controls.DepositHash
