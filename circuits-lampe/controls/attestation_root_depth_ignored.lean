import Deposit.AttestationRoot

namespace Controls.Merkle
open Lampe Determinism Deposit.Commitment Poseidon.Hash2 Merkle.Fold Deposit.AttestationRoot
set_option backward.isDefEq.respectTransparency false

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem attestation_root_depth_ignored {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt ∧ proof_length ≤ 20 ∧
      attestation_root = merkleRoot hash2v
        (hash4 (ownerKey spending_key) attester ((issued_at.toNat : ℕ) : Fp p)
          ((expires_at.toNat : ℕ) : Fp p)) 20 indices path := by
  obtain ⟨hc, hle, st₄, hroot⟩ := accepting_main_rules_eq commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length path
    indices accepts rejects_failure
  obtain ⟨st', st₅, heq⟩ := bmr_pinned_d _ _ _ _ hroot
  exact ⟨hc, hle, (Prod.mk.inj (Option.some.inj heq)).2.symm⟩

#print axioms attestation_root_depth_ignored
end Controls.Merkle
