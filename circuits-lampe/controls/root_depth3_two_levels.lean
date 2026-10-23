import Withdraw.Root

namespace Controls.Merkle
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Merkle.Fold Withdraw.Root
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem root_depth3_two_levels :
    merkleRoot hash2v Withdraw.Nullifier.C0 (3 : U 32) (List.Vector.replicate 32 false)
      (List.Vector.replicate 32 (0 : Fp p)) =
      hash2v (hash2v Withdraw.Nullifier.C0 0) 0 :=
  root_depth3_generic hash2v Withdraw.Nullifier.C0

#print axioms root_depth3_two_levels
end Controls.Merkle
