import Deposit.Steps

/-!
A determinism framework for Lampe's Omni semantics.

`Good p Γ e` says that `e` is built only from deterministic builtins (`BDet`), calls of uniquely
named declarations, `let`, `if` and loops. `Good.inter` proves that two derivations of such an
expression share an outcome. With a forward result (`Omni st e (fun r => r = some (_, v))`) this
pins the value of `e` in every other derivation, which is what a pure equation for a hash needs.
-/

namespace Determinism
open Lampe

/-- A builtin is deterministic at one signature: two derivations share an outcome. -/
def BDet (p : Prime) (b : Builtin) (argTps : List Tp) (outTp : Tp) : Prop :=
  ∀ (st : ValHeap p) (args : HList (Tp.denote p) argTps)
    (Q₁ Q₂ : Option (ValHeap p × Tp.denote p outTp) → Prop),
    b.omni p st argTps outTp args Q₁ → b.omni p st argTps outTp args Q₂ → ∃ r, Q₁ r ∧ Q₂ r

/-- Expressions whose derivations share an outcome. -/
inductive Good (p : Prime) (Γ : Env) : {tp : Tp} → Expr (Tp.denote p) tp → Prop
| litNum {tp n} : Good p Γ (.litNum tp n)
| litStr {len s} : Good p Γ (.litStr len s)
| constFp {c} : Good p Γ (.constFp c)
| constU {w} {c : U w} : Good p Γ (.constU c)
| constI {w} {c : I w} : Good p Γ (.constI c)
| fmtStr {len tps s} : Good p Γ (.fmtStr len tps s)
| fn {a o r} : Good p Γ (.fn a o r)
| var {tp} {v : Tp.denote p tp} : Good p Γ (.var v)
| skip : Good p Γ .skip
| letFn {a o r tp} {b : Tp.denote p (.fn a o) → Expr (Tp.denote p) tp} :
    Good p Γ (b r) → Good p Γ (.letIn (.fn a o r) b)
| letIn {t₁ t₂} {e : Expr (Tp.denote p) t₁} {b : Tp.denote p t₁ → Expr (Tp.denote p) t₂} :
    Good p Γ e → (∀ v, Good p Γ (b v)) → Good p Γ (.letIn e b)
| ite {a c} {t f : Expr (Tp.denote p) a} : Good p Γ t → Good p Γ f → Good p Γ (.ite c t f)
| loop {s r} {lo hi : Tp.denote p (.u s)} {body : Tp.denote p (.u s) → Expr (Tp.denote p) r} :
    (∀ i, Good p Γ (body i)) → Good p Γ (.loop lo hi body)
| builtin {argTps outTp b args} : BDet p b argTps outTp → Good p Γ (.callBuiltin argTps outTp b args)
| call {decl : FunctionDecl} {generics args} : Deposit.Range.UniqueDecl Γ decl →
    Good p Γ ((decl.fn.body (Tp.denote p) generics).body args) → Good p Γ (decl.call generics args)

def Inter (p : Prime) (Γ : Env) {tp} (e : Expr (Tp.denote p) tp) : Prop :=
  ∀ st Q₁ Q₂, Omni p Γ st e Q₁ → Omni p Γ st e Q₂ → ∃ r, Q₁ r ∧ Q₂ r

theorem loop_inter {p Γ s r} {hi : Tp.denote p (.u s)} {body : Tp.denote p (.u s) → Expr (Tp.denote p) r}
    (ih : ∀ i, Inter p Γ (body i)) :
    ∀ (n : ℕ) (lo : Tp.denote p (.u s)), hi.toNat - lo.toNat = n → Inter p Γ (.loop lo hi body) := by
  intro n
  induction n with
  | zero =>
    intro lo hn st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | loopDone hge hq₁ =>
      cases h₂ with
      | loopDone _ hq₂ => exact ⟨_, hq₁, hq₂⟩
      | loopNext hlt _ =>
        exact absurd hge (by simp only [ge_iff_le, BitVec.le_def, not_le]; simp only [BitVec.lt_def] at hlt; omega)
    | loopNext hlt _ =>
      exfalso; simp only [BitVec.lt_def] at hlt; omega
  | succ m ihm =>
    intro lo hn st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | loopDone hge _ =>
      exfalso; simp only [ge_iff_le, BitVec.le_def] at hge; omega
    | loopNext hlt h₁ =>
      cases h₂ with
      | loopDone hge _ =>
        exfalso; simp only [ge_iff_le, BitVec.le_def] at hge; simp only [BitVec.lt_def] at hlt; omega
      | loopNext _ h₂ =>
        cases h₁ with
        | letIn he₁ hb₁ hf₁ =>
          cases h₂ with
          | letIn he₂ hb₂ hf₂ =>
            obtain ⟨r, hr₁, hr₂⟩ := ih lo _ _ _ he₁ he₂
            cases r with
            | none => exact ⟨none, hf₁ hr₁, hf₂ hr₂⟩
            | some sv =>
              obtain ⟨st', v⟩ := sv
              have hlt' := hlt
              simp only [BitVec.lt_def] at hlt'
              have hlo : (lo + 1).toNat = lo.toNat + 1 := by
                rw [BitVec.toNat_add]
                have h2 : hi.toNat < 2 ^ s := hi.isLt
                have h1 : (1 : BitVec s).toNat = 1 := by
                  rw [show (1 : BitVec s) = BitVec.ofNat s 1 from rfl, BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [h1]
                exact Nat.mod_eq_of_lt (by omega)
              exact ihm (lo + 1) (by omega) st' _ _ (hb₁ v st' hr₁) (hb₂ v st' hr₂)

theorem Good.inter {p Γ tp} {e : Expr (Tp.denote p) tp} (hg : Good p Γ e) : Inter p Γ e := by
  induction hg with
  | litNum =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ <;> cases h₂ <;> exact ⟨_, ‹_›, ‹_›⟩
  | litStr =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | litStr hq₁ => cases h₂ with | litStr hq₂ => exact ⟨_, hq₁, hq₂⟩
  | constFp =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | constFp hq₁ => cases h₂ with | constFp hq₂ => exact ⟨_, hq₁, hq₂⟩
  | constU =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | constU hq₁ => cases h₂ with | constU hq₂ => exact ⟨_, hq₁, hq₂⟩
  | constI =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | constI hq₁ => cases h₂ with | constI hq₂ => exact ⟨_, hq₁, hq₂⟩
  | fmtStr =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | fmtStr hq₁ => cases h₂ with | fmtStr hq₂ => exact ⟨_, hq₁, hq₂⟩
  | «fn» =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | «fn» hq₁ => cases h₂ with | «fn» hq₂ => exact ⟨_, hq₁, hq₂⟩
  | var =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | var hq₁ => cases h₂ with | var hq₂ => exact ⟨_, hq₁, hq₂⟩
  | skip =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with | skip hq₁ => cases h₂ with | skip hq₂ => exact ⟨_, hq₁, hq₂⟩
  | letFn _ ih =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | letIn he₁ hb₁ _ =>
      cases h₂ with
      | letIn he₂ hb₂ _ =>
        cases he₁ with
        | «fn» hv₁ =>
          cases he₂ with
          | «fn» hv₂ => exact ih _ _ _ (hb₁ _ _ hv₁) (hb₂ _ _ hv₂)
  | letIn _ _ ihe ihb =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | letIn he₁ hb₁ hf₁ =>
      cases h₂ with
      | letIn he₂ hb₂ hf₂ =>
        obtain ⟨r, hr₁, hr₂⟩ := ihe _ _ _ he₁ he₂
        cases r with
        | none => exact ⟨none, hf₁ hr₁, hf₂ hr₂⟩
        | some sv =>
          obtain ⟨st', v⟩ := sv
          exact ihb v _ _ _ (hb₁ v st' hr₁) (hb₂ v st' hr₂)
  | ite _ _ iht ihf =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | iteTrue h₁ => cases h₂ with | iteTrue h₂ => exact iht _ _ _ h₁ h₂
    | iteFalse h₁ => cases h₂ with | iteFalse h₂ => exact ihf _ _ _ h₁ h₂
  | @loop s r lo hi body _ ih =>
    exact loop_inter ih _ lo rfl
  | builtin hb =>
    intro st Q₁ Q₂ h₁ h₂
    cases h₁ with
    | callBuiltin h₁ =>
      cases h₂ with
      | callBuiltin h₂ =>
        obtain ⟨r, hr₁, hr₂⟩ := hb _ _ _ _ h₁ h₂
        exact ⟨_, hr₁, hr₂⟩
  | call hu _ ih =>
    intro st Q₁ Q₂ h₁ h₂
    exact ih _ _ _ (Deposit.Rules.step_call hu h₁) (Deposit.Rules.step_call hu h₂)

/-- A forward result pins the value of every other accepting derivation. -/
theorem Good.pin {p Γ tp} {e : Expr (Tp.denote p) tp} (hg : Good p Γ e) {st Q} {v : Tp.denote p tp}
    (hfwd : Omni p Γ st e (fun r => ∃ st', r = some (st', v))) (h : Omni p Γ st e Q) :
    ∃ st', Q (some (st', v)) := by
  obtain ⟨r, ⟨st', rfl⟩, hq⟩ := hg.inter st _ _ hfwd h
  exact ⟨st', hq⟩

/-! ## Deterministic builtins -/

theorem pure_inv' {A : Type} {sgn : A → List Tp × Tp} {desc} {p st argTps outTp args Q}
    (h : Builtin.genericPureOmni sgn desc p st argTps outTp args Q) :
    ∃ (a : A) (hA : (sgn a).fst = argTps) (hB : (sgn a).snd = outTp),
      (∃ hh : (desc a (hA ▸ args)).fst, Q (some (st, hB ▸ (desc a (hA ▸ args)).snd hh))) ∨
      (¬ (desc a (hA ▸ args)).fst ∧ Q none) := by
  cases h with
  | ok hh hq => exact ⟨_, rfl, rfl, Or.inl ⟨hh, hq⟩⟩
  | err hn hq => exact ⟨_, rfl, rfl, Or.inr ⟨hn, hq⟩⟩

theorem bdet_pure {A : Type} {sgn : A → List Tp × Tp} {desc} {p argTps outTp}
    (hinj : ∀ a a', (sgn a).fst = (sgn a').fst → (sgn a).snd = (sgn a').snd → a = a') :
    BDet p (Builtin.newGenericPureBuiltin sgn desc) argTps outTp := by
  intro st args Q₁ Q₂ h₁ h₂
  obtain ⟨a₁, hA₁, hB₁, h₁⟩ := pure_inv' h₁
  obtain ⟨a₂, hA₂, hB₂, h₂⟩ := pure_inv' h₂
  obtain rfl := hinj a₁ a₂ (hA₁.trans hA₂.symm) (hB₁.trans hB₂.symm)
  rcases h₁ with ⟨hh₁, hq₁⟩ | ⟨hn₁, hq₁⟩ <;> rcases h₂ with ⟨hh₂, hq₂⟩ | ⟨hn₂, hq₂⟩
  · exact ⟨_, hq₁, hq₂⟩
  · exact absurd hh₁ hn₂
  · exact absurd hh₂ hn₁
  · exact ⟨none, hq₁, hq₂⟩

theorem bdet_cast {p tp tp'} : BDet p Builtin.cast [tp] tp' := by
  intro st args Q₁ Q₂ h₁ h₂
  cases h₁ with
  | ok hq₁ =>
    cases h₂ with
    | ok hq₂ => exact ⟨_, hq₁, hq₂⟩

/-- Unit-indexed pure builtins (`newPureBuiltin`, `newTotalPureBuiltin`). -/
theorem inj_unit {sgn : Unit → List Tp × Tp} :
    ∀ a a', (sgn a).fst = (sgn a').fst → (sgn a).snd = (sgn a').snd → a = a' :=
  fun _ _ _ _ => rfl

/-- Width-indexed builtins whose signature fixes the width through `.u s`. -/
theorem inj_width_out {sgn : ℕ → List Tp × Tp} (h : ∀ s, (sgn s).snd = .u s) :
    ∀ a a', (sgn a).fst = (sgn a').fst → (sgn a).snd = (sgn a').snd → a = a' := by
  intro a a' _ h2
  rw [h, h] at h2
  exact Tp.u.inj h2

theorem inj_width_arg {sgn : ℕ → List Tp × Tp} (h : ∀ s, ∃ rest, (sgn s).fst = .u s :: rest) :
    ∀ a a', (sgn a).fst = (sgn a').fst → (sgn a).snd = (sgn a').snd → a = a' := by
  intro a a' h1 _
  obtain ⟨r, hr⟩ := h a
  obtain ⟨r', hr'⟩ := h a'
  rw [hr, hr'] at h1
  exact Tp.u.inj (List.cons.inj h1).1

#print axioms loop_inter
#print axioms Good.inter
#print axioms Good.pin
#print axioms pure_inv'
#print axioms bdet_pure
#print axioms bdet_cast
#print axioms inj_unit
#print axioms inj_width_out
#print axioms inj_width_arg
end Determinism
