import Withdraw.Nullifier

namespace Controls.Withdraw
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Withdraw.Nullifier

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_poseidon2_pinned_swapped {st Q} (a b : Fp p)
    (h : Omni p Γw st («withdraw-0.0.0::poseidon2».call h![] h![a, b]) Q) :
    ∃ st', Q (some (st', hash2v b a)) :=
  (wgood_poseidon2 bn254_gt a b).pin (poseidon2_fwd st a b) h

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

#print axioms withdraw_poseidon2_pinned_swapped
end Controls.Withdraw
