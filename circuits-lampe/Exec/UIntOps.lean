import Exec.ArrayOps
namespace Exec.UIntOps
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem add {p Γ st w} (a b : U w) (h : a.toNat+b.toNat < 2^w) :
    Omni p Γ st (.callBuiltin [.u w,.u w] (.u w) Builtin.uAdd h![a,b])
      (fun r => r = some (st,a+b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) h rfl

theorem mul {p Γ st w} (a b : U w) (h : a.toNat*b.toNat < 2^w) :
    Omni p Γ st (.callBuiltin [.u w,.u w] (.u w) Builtin.uMul h![a,b])
      (fun r => r = some (st,a*b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) h rfl

theorem sub {p Γ st w} (a b : U w) (h : b ≤ a) :
    Omni p Γ st (.callBuiltin [.u w,.u w] (.u w) Builtin.uSub h![a,b])
      (fun r => r = some (st,a-b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) h rfl

theorem cast8_32 {p Γ st} (a : U 8) :
    Omni p Γ st (.callBuiltin [.u 8] (.u 32) Builtin.cast h![a])
      (fun r => r = some (st, (a.toNat : U 32))) := by
  apply Omni.callBuiltin
  apply Builtin.castOmni.ok
  have hc : a.setWidth 32 = (a.toNat : U 32) := by
    apply BitVec.eq_of_toNat_eq
    simp
  change some (st,a.setWidth 32) = some (st,(a.toNat : U 32))
  rw [hc]

theorem array_len {p Γ st tp} (n : U 32) (v : List.Vector (Tp.denote p tp) n.toNat) :
    Omni p Γ st (.callBuiltin [.array tp n] (.u 32) Builtin.arrayLen h![v])
      (fun r => r = some (st,n)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := Builtin.ArrayLenCase.array tp n) True.intro rfl

theorem witness {p Γ st} (v : Fp p) :
    Omni p Γ st (.callBuiltin [.field] .unit Builtin.asWitness h![v])
      (fun r => r = some (st,())) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

theorem div {p Γ st w} (a b : U w) (h : b ≠ 0) :
    Omni p Γ st (.callBuiltin [.u w,.u w] (.u w) Builtin.uDiv h![a,b])
      (fun r => r = some (st,a.udiv b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) h rfl

theorem bitand {p Γ st w} (a b : U w) :
    Omni p Γ st (.callBuiltin [.u w,.u w] (.u w) Builtin.uAnd h![a,b])
      (fun r => r = some (st,a &&& b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) True.intro rfl

theorem eq {p Γ st w} (a b : U w) :
    Omni p Γ st (.callBuiltin [.u w,.u w] .bool Builtin.uEq h![a,b])
      (fun r => r = some (st,decide (a=b))) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := w) True.intro rfl

theorem castField32 {p Γ st} (a : Fp p) :
    Omni p Γ st (.callBuiltin [.field] (.u 32) Builtin.cast h![a])
      (fun r => r = some (st,(a.val : U 32))) := by
  apply Omni.callBuiltin
  exact Builtin.castOmni.ok rfl

#print axioms div
#print axioms bitand
#print axioms eq
#print axioms castField32
#print axioms add
#print axioms mul
#print axioms sub
#print axioms cast8_32
#print axioms array_len
#print axioms witness
end Exec.UIntOps
