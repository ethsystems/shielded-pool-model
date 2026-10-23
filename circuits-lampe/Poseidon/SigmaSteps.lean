import Exec.Basic
namespace Poseidon.SigmaSteps
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem sigma2 {p Γ st} (a b : Fp p)
    (hm : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::sigma».call h![(2 : U 32)] h![(⟨[a,b], rfl⟩ : List.Vector (Fp p) 2)])
      (fun r => ∃ st', r = some (st', (⟨[a * ((a*a)*(a*a)), b * ((b*b)*(b*b))], rfl⟩ : List.Vector (Fp p) 2))) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::sigma»]
  repeat' ((try dsimp only [mapToValHeapCondition]); first
    | (solve | decide +kernel)
    | exec_pure
    | (apply bind_ref; intro addr hfresh)
    | (apply bind_read; exact Finmap.lookup_insert _)
    | (apply bind_write; exact Finmap.lookup_insert _)
    | (apply bind_cps)
    | (apply Omni.loopNext; · exact of_decide_eq_true rfl)
    | (apply Omni.loopDone; · exact of_decide_eq_true rfl)
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.field, (2 : U 32))))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ()))
    | (apply Omni.callBuiltin; apply Builtin.castOmni.ok)
    | (apply Omni.callBuiltin; apply Builtin.readRefOmni.mk; · exact Finmap.lookup_insert _)
    | (apply Omni.callBuiltin
       apply Builtin.modifyLensOmni.ok (hr := rfl)
       · exact Finmap.lookup_insert _
       · rfl
       · rfl
       · rfl)
    | (apply Omni.skip)
    | (apply Omni.var)
    | (apply Omni.constU)
    | (apply Omni.litU)
    | (apply Omni.litField)
    | (refine ⟨_, rfl⟩)
    | trivial)
  all_goals try first
    | trivial
    | (change (0 : U 32).toNat < (2 : U 32).toNat; decide)
    | (change (1 : U 32).toNat < (2 : U 32).toNat; decide)
  all_goals
    dsimp [mapToValHeapCondition, RefPath.get, RefPath.modify, Builtin.CastTp.cast]
    exact ⟨_, rfl⟩
theorem sigma5 {p Γ st} (a b c d e : Fp p)
    (hm : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::sigma».call h![(5 : U 32)] h![(⟨[a,b,c,d,e], rfl⟩ : List.Vector (Fp p) 5)])
      (fun r => ∃ st', r = some (st', (⟨[a * ((a*a)*(a*a)), b * ((b*b)*(b*b)), c * ((c*c)*(c*c)), d * ((d*d)*(d*d)), e * ((e*e)*(e*e))], rfl⟩ : List.Vector (Fp p) 5))) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::sigma»]
  repeat' ((try dsimp only [mapToValHeapCondition]); first
    | (solve | decide +kernel)
    | exec_pure
    | (apply bind_ref; intro addr hfresh)
    | (apply bind_read; exact Finmap.lookup_insert _)
    | (apply bind_write; exact Finmap.lookup_insert _)
    | (apply bind_cps)
    | (apply Omni.loopNext; · exact of_decide_eq_true rfl)
    | (apply Omni.loopDone; · exact of_decide_eq_true rfl)
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.field, (5 : U 32))))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ()))
    | (apply Omni.callBuiltin; apply Builtin.castOmni.ok)
    | (apply Omni.callBuiltin; apply Builtin.readRefOmni.mk; · exact Finmap.lookup_insert _)
    | (apply Omni.callBuiltin
       apply Builtin.modifyLensOmni.ok (hr := rfl)
       · exact Finmap.lookup_insert _
       · rfl
       · rfl
       · rfl)
    | (apply Omni.skip)
    | (apply Omni.var)
    | (apply Omni.constU)
    | (apply Omni.litU)
    | (apply Omni.litField)
    | (refine ⟨_, rfl⟩)
    | trivial)
  all_goals try first
    | trivial
    | (change (0 : U 32).toNat < (5 : U 32).toNat; decide)
    | (change (1 : U 32).toNat < (5 : U 32).toNat; decide)
    | (change (2 : U 32).toNat < (5 : U 32).toNat; decide)
    | (change (3 : U 32).toNat < (5 : U 32).toNat; decide)
    | (change (4 : U 32).toNat < (5 : U 32).toNat; decide)
  all_goals
    dsimp [mapToValHeapCondition, RefPath.get, RefPath.modify, Builtin.CastTp.cast]
    exact ⟨_, rfl⟩
#print axioms sigma5
#print axioms sigma2
end Poseidon.SigmaSteps
