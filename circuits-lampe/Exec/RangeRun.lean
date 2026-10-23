import Exec.Run
import Lampe.Crypto.Bn254.Prime
namespace Exec.RangeRun
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

theorem zero_range {Γ st}
    (hm : «std-1.0.0-beta.21::field::assert_max_bit_size» ∈ Γ.functions) :
    Omni p Γ st
      («std-1.0.0-beta.21::field::assert_max_bit_size».call h![(128 : U 32)] h![(0 : Fp p)])
      (fun r => r = some (st, ())) := by
  apply call _ _ _ hm
  dsimp only [«std-1.0.0-beta.21::field::assert_max_bit_size»]
  run_steps
  apply Omni.callBuiltin
  apply Builtin.genericPureOmni.ok (a := ((43 : U 32), Tp.u 8))
  all_goals run_steps
  all_goals first | rfl | exact () | trivial | (change (0 : Fp p).val < 2^128; decide +kernel)
#print axioms zero_range
end Exec.RangeRun
