import Deposit.Commitment

namespace Controls.DepositHash
open Lampe Determinism Deposit.Commitment

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem same_deposit_poseidon4_pinned {st Q} (a b c d : Fp p)
    (h : Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', hash4 a b c d)) :=
  (good_poseidon4 bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

#print axioms same_deposit_poseidon4_pinned
end Controls.DepositHash
