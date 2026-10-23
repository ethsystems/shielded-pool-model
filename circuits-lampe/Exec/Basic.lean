import «deposit-0.0.0».Extracted
import Lampe

namespace Exec.Basic
open Lampe

theorem bind_value {p Γ st st' tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {v Q}
    (he : Omni p Γ st e (fun r => r = some (st', v)))
    (hb : Omni p Γ st' (b v) Q) : Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn he
  · intro v' st'' h
    cases Option.some.inj h
    exact hb
  · intro h
    cases h

theorem bind_cps {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st e (fun r => match r with
      | none => Q none
      | some (st', v) => Omni p Γ st' (b v) Q)) :
    Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn h
  · intro _ _ h; exact h
  · intro h; exact h

theorem bind_result {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {v Q}
    (he : Omni p Γ st e (fun r => ∃ st', r = some (st', v)))
    (next : ∀ st', Omni p Γ st' (b v) Q) : Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn he
  · rintro _ _ ⟨st', h⟩
    cases Option.some.inj h
    exact next _
  · rintro ⟨_, h⟩; cases h

theorem loop_noop32 {p Γ st} (lo hi : U 32)
    (body : U 32 → Expr (Tp.denote p) .unit)
    (hbody : ∀ i, Omni p Γ st (body i) (fun r => r = some (st, ()))) :
    Omni p Γ st (.loop lo hi body) (fun r => r = some (st, ())) := by
  generalize hn : hi.toNat - lo.toNat = n
  induction n generalizing lo with
  | zero =>
    apply Omni.loopDone
    · change hi.toNat ≤ lo.toNat
      omega
    · rfl
  | succ n ih =>
    have hlt : lo < hi := by
      change lo.toNat < hi.toNat
      omega
    apply Omni.loopNext hlt
    apply bind_value (hbody lo)
    apply ih
    have hval : (lo + 1).toNat = lo.toNat + 1 := by
      have hh := hi.isLt
      change lo.toNat < hi.toNat at hlt
      change (lo.toNat + 1) % 2^32 = lo.toNat + 1
      exact Nat.mod_eq_of_lt (by omega)
    omega

theorem bind_pure {A : Type} {sgn : A → List Tp × Tp} {desc p Γ st a args tp}
    {b : Tp.denote p (sgn a).snd → Expr (Tp.denote p) tp} {Q}
    (h : (desc a args).fst)
    (next : Omni p Γ st (b ((desc a args).snd h)) Q) :
    Omni p Γ st (.letIn (.callBuiltin (sgn a).fst (sgn a).snd
      (Builtin.newGenericPureBuiltin sgn desc) args) b) Q := by
  apply bind_value (v := (desc a args).snd h) ?_ next
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok h rfl

theorem bind_ref {p Γ st tp tp'} {v : Tp.denote p tp}
    {b : Ref tp → Expr (Tp.denote p) tp'} {Q}
    (next : ∀ addr, addr ∉ st.vals →
      Omni p Γ ⟨st.vals.insert addr ⟨tp, v⟩, st.lambdas⟩ (b (Ref.mk tp addr .nil)) Q) :
    Omni p Γ st (.letIn (.callBuiltin [tp] (.ref tp) Builtin.ref h![v]) b) Q := by
  apply Omni.letIn (Q₁ := fun r => ∃ addr, addr ∉ st.vals ∧
    r = some (⟨st.vals.insert addr ⟨tp, v⟩, st.lambdas⟩, Ref.mk tp addr .nil))
  · apply Omni.callBuiltin
    apply Builtin.refOmni.mk
    intro addr h
    exact ⟨addr, h, rfl⟩
  · rintro _ _ ⟨addr, hfresh, h⟩
    cases Option.some.inj h
    exact next addr hfresh
  · rintro ⟨_, _, h⟩
    cases h

theorem bind_read {p Γ st tp tp'} {ref : Ref tp} {value : Tp.denote p ref.base_tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q}
    (lookup : st.vals.lookup ref.addr = some ⟨ref.base_tp, value⟩)
    (next : Omni p Γ st (b (RefPath.get p ref.path value)) Q) :
    Omni p Γ st (.letIn (.callBuiltin [.ref tp] tp Builtin.readRef h![ref]) b) Q := by
  apply bind_value ?_ next
  apply Omni.callBuiltin
  exact Builtin.readRefOmni.mk lookup rfl

theorem bind_write {p Γ st tp tp'} {ref : Ref tp} {value : Tp.denote p ref.base_tp}
    {v : Tp.denote p tp} {b : Unit → Expr (Tp.denote p) tp'} {Q}
    (lookup : st.vals.lookup ref.addr = some ⟨ref.base_tp, value⟩)
    (next : Omni p Γ ⟨st.vals.insert ref.addr ⟨ref.base_tp, RefPath.modify p ref.path value v⟩,
      st.lambdas⟩ (b ()) Q) :
    Omni p Γ st (.letIn (.callBuiltin [.ref tp, tp] .unit Builtin.writeRef h![ref,v]) b) Q := by
  apply bind_value (tp := .unit) (v := ()) ?_ next
  apply Omni.callBuiltin
  exact Builtin.writeRefOmni.mk lookup rfl

theorem bind_modify {p Γ st tp tp' outTp} {ref : Ref tp}
    {value : Tp.denote p ref.base_tp} {v : Tp.denote p tp'}
    {lens : Lens (Tp.denote p) tp tp'} {updated : Tp.denote p tp}
    {b : Unit → Expr (Tp.denote p) outTp} {Q}
    (lookup : st.vals.lookup ref.addr = some ⟨ref.base_tp, value⟩)
    (hmodify : some updated = lens.modify (RefPath.get p ref.path value) v)
    (next : Omni p Γ ⟨st.vals.insert ref.addr ⟨ref.base_tp,
      RefPath.modify p ref.path value updated⟩, st.lambdas⟩ (b ()) Q) :
    Omni p Γ st (.letIn (.callBuiltin [.ref tp, tp'] .unit
      (Builtin.modifyLens lens) h![ref,v]) b) Q := by
  apply bind_value (tp := .unit) (v := ()) ?_ next
  apply Omni.callBuiltin
  exact Builtin.modifyLensOmni.ok (hr := rfl) lookup rfl hmodify rfl rfl

theorem call {p Γ st} (d : FunctionDecl) (generics) (args)
    {Q : Option (State p × Tp.denote p (d.fn.body (Tp.denote p) generics).outTp) → Prop}
    (hmem : d ∈ Γ.functions)
    (hbody : Omni p Γ st ((d.fn.body (Tp.denote p) generics).body args) Q) :
    Omni p Γ st (d.call generics args) Q := by
  exact Omni.callDecl rfl hmem rfl rfl rfl hbody

macro "exec_pure" : tactic => `(tactic|
  first
  | (apply bind_pure <;> try (first | trivial | exact of_decide_eq_true rfl | assumption))
  | (apply bind_value; · apply Omni.fn; rfl)
  | (apply bind_value; · apply Omni.constU; rfl)
  | (apply bind_value; · apply Omni.litU; rfl)
  | (apply bind_value; · apply Omni.litField; rfl)
  | (apply bind_value; · apply Omni.var; rfl)
  | (apply bind_value; · apply Omni.skip; rfl)
  | (apply bind_value; · apply Omni.callBuiltin; apply Builtin.castOmni.ok; rfl))

#print axioms bind_result
#print axioms loop_noop32
#print axioms bind_cps
#print axioms bind_value
#print axioms bind_pure
#print axioms bind_ref
#print axioms bind_read
#print axioms bind_write
#print axioms bind_modify
#print axioms call
end Exec.Basic
