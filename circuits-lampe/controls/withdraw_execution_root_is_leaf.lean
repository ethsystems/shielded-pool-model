import Withdraw.Root

namespace Controls.Merkle
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Merkle.Fold Withdraw.Root
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_execution_root_is_leaf (st : State p) (d : U 32) (hd : d ≤ 32)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32) :
    Omni p Γw st («withdraw-0.0.0::main».call h![]
      h![Withdraw.Nullifier.N0, (0 : Fp p), (0 : Fp p), (0 : Fp p),
        Withdraw.Nullifier.C0, (0 : Fp p), (0 : Fp p), d, path, indices])
      (fun r => ∃ st', r = some (st', ())) :=
  main_from_fwd_d st _ _ _ _ d path indices (fun st => poseidon1_fwd st 0) poseidon4_fwd poseidon2_fwd
    (fun _ => verify_fwd_w _ d hd path indices)

#print axioms withdraw_execution_root_is_leaf
end Controls.Merkle
