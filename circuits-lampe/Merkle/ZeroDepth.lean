import Exec.Run
namespace Merkle.ZeroDepth
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem lt_zero32 {p Γ st} (i : U 32) :
    Omni p Γ st (.callBuiltin [.u 32, .u 32] .bool Builtin.uLt h![i, (0 : U 32)])
      (fun r => r = some (st, false)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := 32) True.intro (by simp [BitVec.lt_def]; rfl)

theorem root_zero_depth {p Γ st} (leaf : Fp p)
    (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)
    (hasher : FuncRef [.array .field 2] .field)
    (hm : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ Γ.functions) :
    Omni p Γ st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
        h![hasher, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', leaf)) := by
  apply call _ _ _ hm
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  repeat' first
    | exec_pure
    | (apply bind_ref; intro addr hfresh)
  apply bind_value (loop_noop32 _ _ _ ?_)
  · run_steps
    all_goals try first | rfl | exact () | trivial
    all_goals
      dsimp [mapToValHeapCondition, RefPath.get]
      exact ⟨_, rfl⟩
  · intro i
    repeat' first
      | apply bind_value (lt_zero32 _)
      | exec_pure
      | apply Omni.iteFalse
      | apply Omni.skip
      | rfl

#print axioms lt_zero32
#print axioms root_zero_depth
end Merkle.ZeroDepth
