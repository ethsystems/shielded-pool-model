import Determinism
import Deposit.Steps

/-!
Inversion steps the transfer `main` needs beyond `Deposit.Steps` and `Deposit.PinnedCast`: the `u128` cast to
`Field` (patched Lampe: one cast function per type pair), `u128` equality, boolean negation,
`if` without `else`, and two sequencing lemmas for `Good` expressions.
-/

namespace Transfer.CastSteps
open Lampe Deposit.Rules Determinism

/-- Every derivation of `v as Field` for `v : u128` returns `v.toNat` in the input state. -/
theorem cast_u128_field {p Γ st} {v : U 128} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 128] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

theorem step_cast_u128 {p Γ st tp''} {v : U 128}
    {b : Tp.denote p .field → Expr (Tp.denote p) tp''} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.u 128] .field Builtin.cast h![v]) b) Q) :
    Omni p Γ st (b ((v.toNat : ℕ) : Fp p)) Q := by
  cases h with
  | letIn he hb _ => exact hb _ _ (cast_u128_field he)

theorem step_litU {p Γ st w tp'} {n : Int}
    {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.litNum (.u w) n) b) Q) : Omni p Γ st (b (BitVec.ofInt w n)) Q := by
  cases h with
  | letIn he hb _ => cases he with | litU hv => exact hb _ _ hv

theorem step_uEq {p Γ st w tp'} {a c : U w}
    {b : Tp.denote p .bool → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.u w, .u w] .bool Builtin.uEq h![a, c]) b) Q)
    (hn : ¬ Q none) : Omni p Γ st (b (decide (a = c))) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨s, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · simp only [List.cons.injEq, Tp.u.injEq, and_true] at hA
        obtain ⟨rfl, -⟩ := hA
        exact hb _ _ hq

theorem step_bNot {p Γ st tp'} {a : Bool}
    {b : Tp.denote p .bool → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.bool] .bool Builtin.bNot h![a]) b) Q)
    (hn : ¬ Q none) : Omni p Γ st (b (!a)) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨_, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · exact hb _ _ hq

theorem ite_true_inv {p Γ st tp} {t f : Expr (Tp.denote p) tp} {Q}
    (h : Omni p Γ st (.ite true t f) Q) : Omni p Γ st t Q := by
  cases h with | iteTrue h => exact h

theorem ite_false_inv {p Γ st tp} {t f : Expr (Tp.denote p) tp} {Q}
    (h : Omni p Γ st (.ite false t f) Q) : Omni p Γ st f Q := by
  cases h with | iteFalse h => exact h

/-- A `Good` expression in an accepting `let` has an outcome that carries the continuation. -/
theorem good_letIn {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q} (hg : Good p Γ e)
    (h : Omni p Γ st (.letIn e b) Q) (hn : ¬ Q none) :
    ∃ Q₁, Omni p Γ st e Q₁ ∧ ¬ Q₁ none ∧ ∃ st' v, Q₁ (some (st', v)) ∧ Omni p Γ st' (b v) Q := by
  obtain ⟨Q₁, he, hn₁, hk⟩ := letIn_inv h hn
  obtain ⟨r, hr, -⟩ := hg.inter st _ _ he he
  cases r with
  | none => exact absurd hr hn₁
  | some sv =>
    obtain ⟨st', v⟩ := sv
    exact ⟨Q₁, he, hn₁, st', v, hr, hk v st' hr⟩

/-- A `Good` expression with a forward result `v`, in an accepting `let`: the continuation runs on `v`. -/
theorem pin_letIn {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q} {v : Tp.denote p tp} (hg : Good p Γ e)
    (hfwd : Omni p Γ st e (fun r => ∃ st', r = some (st', v)))
    (h : Omni p Γ st (.letIn e b) Q) (hn : ¬ Q none) :
    ∃ st', Omni p Γ st' (b v) Q := by
  obtain ⟨st', st'', v', heq, hb⟩ := hg.pin hfwd (step_seq h hn)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  exact ⟨st', hb⟩

#print axioms cast_u128_field
#print axioms step_cast_u128
#print axioms step_litU
#print axioms step_uEq
#print axioms step_bNot
#print axioms ite_true_inv
#print axioms ite_false_inv
#print axioms good_letIn
#print axioms pin_letIn
end Transfer.CastSteps
