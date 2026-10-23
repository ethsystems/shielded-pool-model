import Exec.Run
namespace Poseidon.MatrixSteps
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem matrix2 {p Γ st} (a b m00 m01 m10 m11 : Fp p)
    (hm : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st
      («poseidon-0.0.0::poseidon::apply_matrix».call h![(2 : U 32)]
        h![(⟨[⟨[m00,m01], rfl⟩, ⟨[m10,m11], rfl⟩], rfl⟩ : List.Vector (List.Vector (Fp p) 2) 2),
          (⟨[a,b], rfl⟩ : List.Vector (Fp p) 2)])
      (fun r => ∃ st', r = some (st', (⟨[0 + a*m00 + b*m10, 0 + a*m01 + b*m11], rfl⟩ : List.Vector (Fp p) 2))) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::apply_matrix»]
  repeat' first
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((2 : U 32), Tp.field)))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.field, (2 : U 32))))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.array Tp.field 2, (2 : U 32))))
  all_goals try first
    | rfl | exact () | trivial
    | (change (0 : U 32).toNat < (2 : U 32).toNat; decide)
    | (change (1 : U 32).toNat < (2 : U 32).toNat; decide)
  all_goals
    dsimp [mapToValHeapCondition, RefPath.get, RefPath.modify, Builtin.CastTp.cast]
    exact ⟨_, rfl⟩
#print axioms matrix2
end Poseidon.MatrixSteps
