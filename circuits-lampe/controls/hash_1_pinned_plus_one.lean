import Deposit.Commitment

namespace Controls.DepositHash
open Lampe Determinism Deposit.Commitment

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem hash_1_pinned_plus_one {st Q} (sk : Fp p)
    (h : Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[sk], rfl⟩ : List.Vector (Fp p) 1)]) Q) : ∃ st', Q (some (st', ownerKey (sk + 1))) :=
  (good_hash_1 bn254_gt _).pin (hash_1_fwd st sk) h

#print axioms hash_1_pinned_plus_one
end Controls.DepositHash
