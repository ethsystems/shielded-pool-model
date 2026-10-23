import Exec.Heap
namespace Exec.ArrayOps
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

theorem index {p Γ st tp} {n : U 32} (v : List.Vector (Tp.denote p tp) n.toNat)
    (i : U 32) (hi : i.toNat < n.toNat) :
    Omni p Γ st (.callBuiltin [.array tp n, .u 32] tp Builtin.arrayIndex h![v,i])
      (fun r => r = some (st,v.get ⟨i.toNat,hi⟩)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := (tp,n)) hi rfl

theorem cast32 {p Γ st} (i : U 32) :
    Omni p Γ st (.callBuiltin [.u 32] (.u 32) Builtin.cast h![i])
      (fun r => r = some (st,i)) := by
  apply Omni.callBuiltin
  apply Builtin.castOmni.ok
  simp [mapToValHeapCondition, Builtin.CastTp.cast]

theorem mul {p Γ st} (a b : Fp p) :
    Omni p Γ st (.callBuiltin [.field, .field] .field Builtin.fMul h![a,b])
      (fun r => r = some (st,a*b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

#print axioms mul
theorem add {p Γ st} (a b : Fp p) :
    Omni p Γ st (.callBuiltin [.field, .field] .field Builtin.fAdd h![a,b])
      (fun r => r = some (st,a+b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

#print axioms add
theorem sub {p Γ st} (a b : Fp p) :
    Omni p Γ st (.callBuiltin [.field, .field] .field Builtin.fSub h![a,b])
      (fun r => r = some (st,a-b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

#print axioms sub
#print axioms index
#print axioms cast32
end Exec.ArrayOps
