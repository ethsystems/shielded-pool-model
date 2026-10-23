import Deposit.Range

/-! Inversion steps for accepting Omni derivations (every accepting execution). -/

namespace Deposit.Rules
open Lampe

/-! ## Inversion steps -/

theorem letIn_inv {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn e b) Q) (hn : ¬ Q none) :
    ∃ Q₁, Omni p Γ st e Q₁ ∧ ¬ Q₁ none ∧ ∀ v st', Q₁ (some (st', v)) → Omni p Γ st' (b v) Q := by
  cases h with
  | letIn he hb hf => exact ⟨_, he, fun h0 => hn (hf h0), hb⟩

-- Every outcome of `e` carries a derivation of the continuation.
theorem step_seq {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn e b) Q) (hn : ¬ Q none) :
    Omni p Γ st e (fun r => ∃ st' v, r = some (st', v) ∧ Omni p Γ st' (b v) Q) := by
  obtain ⟨Q₁, he, hn₁, hb⟩ := letIn_inv h hn
  apply Omni.consequence he
  intro r hr
  cases r with
  | none => exact absurd hr hn₁
  | some sv =>
    obtain ⟨st', v⟩ := sv
    exact ⟨st', v, rfl, hb v st' hr⟩

theorem step_fn {p Γ st tp' argTps outTp} {r : FuncRef argTps outTp}
    {b : Tp.denote p (.fn argTps outTp) → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.fn argTps outTp r) b) Q) : Omni p Γ st (b r) Q := by
  cases h with
  | letIn he hb _ => cases he with | «fn» hv => exact hb _ _ hv

theorem step_var {p Γ st tp tp'} {v : Tp.denote p tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.var v) b) Q) : Omni p Γ st (b v) Q := by
  cases h with
  | letIn he hb _ => cases he with | var hv => exact hb _ _ hv

theorem step_constU {p Γ st w tp'} {c : U w}
    {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.constU c) b) Q) : Omni p Γ st (b c) Q := by
  cases h with
  | letIn he hb _ => cases he with | constU hv => exact hb _ _ hv

-- Generic inversion of a pure builtin, with the value it returns.
theorem pure_inv {A : Type} {sgn : A → List Tp × Tp} {desc} {p st argTps outTp args Q}
    (h : Builtin.genericPureOmni sgn desc p st argTps outTp args Q) :
    Q none ∨ ∃ (a : A) (hA : (sgn a).fst = argTps) (hB : (sgn a).snd = outTp)
      (hh : (desc a (hA ▸ args)).fst), Q (some (st, hB ▸ (desc a (hA ▸ args)).snd hh)) := by
  cases h with
  | ok hh hq => exact Or.inr ⟨_, rfl, rfl, hh, hq⟩
  | err _ hq => exact Or.inl hq

theorem step_fEq {p Γ st tp'} {a c : Fp p}
    {b : Tp.denote p .bool → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.field, .field] .bool Builtin.fEq h![a, c]) b) Q)
    (hn : ¬ Q none) : Omni p Γ st (b (decide (a = c))) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨_, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · exact hb _ _ hq

theorem step_uLeq {p Γ st tp'} {a c : U 32}
    {b : Tp.denote p .bool → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.u 32, .u 32] .bool Builtin.uLeq h![a, c]) b) Q)
    (hn : ¬ Q none) : Omni p Γ st (b (decide (a ≤ c))) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨s, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · simp only [List.cons.injEq, Tp.u.injEq, and_true] at hA
        obtain ⟨rfl, -⟩ := hA
        exact hb _ _ hq

theorem step_assert {p Γ st tp'} {c : Bool}
    {b : Tp.denote p .unit → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.bool] .unit Builtin.assert h![c]) b) Q)
    (hn : ¬ Q none) : c = true ∧ Omni p Γ st (b ()) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨_, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · exact ⟨by simpa using hh, hb _ _ hq⟩

theorem step_mkArray1 {p Γ st tp'} {a : Fp p}
    {b : Tp.denote p (.array .field 1) → Expr (Tp.denote p) tp'} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [.field] (.array .field 1) Builtin.mkArray h![a]) b) Q)
    (hn : ¬ Q none) : Omni p Γ st (b ⟨[a], rfl⟩) Q := by
  cases h with
  | letIn he hb hf =>
    cases he with
    | callBuiltin he =>
      rcases pure_inv he with h0 | ⟨⟨n, t⟩, hA, hB, hh, hq⟩
      · exact absurd (hf h0) hn
      · change Tp.array t n = Tp.array Tp.field 1 at hB
        injection hB with ht hn'
        subst ht
        subst hn'
        exact hb _ _ hq

-- The cast builtin takes its CastTp instance as a constructor argument, so the derivation fixes it.
theorem step_cast {p Γ st tp tp' tp''} {v : Tp.denote p tp}
    {b : Tp.denote p tp' → Expr (Tp.denote p) tp''} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [tp] tp' Builtin.cast h![v]) b) Q) :
    ∃ c : Builtin.CastTp tp tp', Omni p Γ st (b (@Builtin.CastTp.cast tp tp' c p v)) Q := by
  cases h with
  | letIn he hb _ =>
    cases he with
    | callBuiltin he =>
      cases he with
      | ok hv => exact ⟨_, hb _ _ hv⟩

theorem step_decl {p Γ kinds} {generics : HList Kind.denote kinds} {argTps outTp args fnName st Q}
    (h : Omni p Γ st (.call argTps outTp (.decl fnName kinds generics) args) Q) :
    ∃ f, ⟨fnName, f⟩ ∈ Γ.functions ∧ ∃ (hk : f.generics = kinds)
      (hi : (f.body (Tp.denote p) (hk ▸ generics)).argTps = argTps)
      (ho : (f.body (Tp.denote p) (hk ▸ generics)).outTp = outTp),
      Omni p Γ st (ho ▸ (f.body (Tp.denote p) (hk ▸ generics)).body (hi ▸ args)) Q := by
  cases h with
  | callTrait href _ _ _ _ _ => cases href
  | callLambda href _ _ => cases href
  | callDecl href hmem hk hi ho he =>
    cases href
    exact ⟨_, hmem, hk, hi, ho, he⟩

theorem step_call {p Γ decl generics args st Q} (unique : Deposit.Range.UniqueDecl Γ decl)
    (h : Omni p Γ st (decl.call generics args) Q) :
    Omni p Γ st ((decl.fn.body (Tp.denote p) generics).body args) Q := by
  obtain ⟨f, hm, hk, hi, ho, he⟩ := step_decl h
  unfold Deposit.Range.UniqueDecl at unique
  have heq := unique f hm
  subst heq
  simpa using he

/-! ## The range call has an outcome in every accepting derivation -/

@[irreducible] def Wit (p : Prime) (Γ : Env) {tp} (e : Expr (Tp.denote p) tp) : Prop :=
  ∀ st Q, Omni p Γ st e Q → ¬ Q none → ∃ st' v, Q (some (st', v))

theorem wit_letIn {p Γ tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'}
    (he : Wit p Γ e) (hb : ∀ v, Wit p Γ (b v)) : Wit p Γ (.letIn e b) := by
  unfold Wit at *
  intro st Q h hn
  obtain ⟨Q₁, h1, hn₁, hk⟩ := letIn_inv h hn
  obtain ⟨st', v, hq⟩ := he st Q₁ h1 hn₁
  exact hb v st' Q (hk v st' hq) hn

theorem wit_pure {A : Type} {sgn : A → List Tp × Tp} {desc p Γ argTps outTp args} :
    Wit p Γ (.callBuiltin argTps outTp (Builtin.newGenericPureBuiltin sgn desc) args) := by
  unfold Wit at *
  intro st Q h hn
  rcases Deposit.Range.pure_outcome h with h0 | ⟨v, hv⟩
  · exact absurd h0 hn
  · exact ⟨st, v, hv⟩

theorem wit_cast {p Γ tp tp'} {v : Tp.denote p tp} :
    Wit p Γ (.callBuiltin [tp] tp' Builtin.cast h![v]) := by
  unfold Wit at *
  intro st Q h _
  cases h with
  | callBuiltin h => cases h with | ok hv => exact ⟨_, _, hv⟩

theorem wit_constU {p Γ w} {c : U w} : Wit p Γ (.constU c) := by
  unfold Wit at *
  intro st Q h _
  cases h with | constU hv => exact ⟨_, _, hv⟩

theorem wit_litU {p Γ w} {n : Int} : Wit p Γ (.litNum (.u w) n) := by
  unfold Wit at *
  intro st Q h _
  cases h with | litU hv => exact ⟨_, _, hv⟩

theorem wit_skip {p Γ} : Wit p Γ (.skip : Expr (Tp.denote p) .unit) := by
  unfold Wit at *
  intro st Q h _
  cases h with | skip hv => exact ⟨_, _, hv⟩

theorem wit_call {p Γ decl generics args} (unique : Deposit.Range.UniqueDecl Γ decl)
    (hb : Wit p Γ ((decl.fn.body (Tp.denote p) generics).body args)) :
    Wit p Γ (decl.call generics args) := by
  unfold Wit at *
  intro st Q h hn
  exact hb st Q (step_call unique h) hn


theorem Wit.run {p Γ tp} {e : Expr (Tp.denote p) tp} (h : Wit p Γ e) {st Q}
    (ho : Omni p Γ st e Q) (hn : ¬ Q none) : ∃ st' v, Q (some (st', v)) := by
  unfold Wit at h
  exact h st Q ho hn

theorem wit_let_pure {A : Type} {sgn : A → List Tp × Tp} {desc p Γ argTps outTp args tp}
    {b : Tp.denote p outTp → Expr (Tp.denote p) tp}
    (next : ∀ v, Wit p Γ (b v)) :
    Wit p Γ (.letIn (.callBuiltin argTps outTp (Builtin.newGenericPureBuiltin sgn desc) args) b) :=
  wit_letIn wit_pure next

theorem wit_let_cast {p Γ tp₀ tp' tp} {v : Tp.denote p tp₀}
    {b : Tp.denote p tp' → Expr (Tp.denote p) tp}
    (next : ∀ v, Wit p Γ (b v)) :
    Wit p Γ (.letIn (.callBuiltin [tp₀] tp' Builtin.cast h![v]) b) :=
  wit_letIn wit_cast next

theorem wit_let_constU {p Γ w tp} {c : U w} {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp}
    (next : Wit p Γ (b c)) : Wit p Γ (.letIn (.constU c) b) := by
  unfold Wit at *
  intro st Q h hn
  exact next st Q (step_constU h) hn

theorem wit_let_litU {p Γ w tp} {n : Int} {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp}
    (next : Wit p Γ (b (BitVec.ofInt w n))) : Wit p Γ (.letIn (.litNum (.u w) n) b) := by
  unfold Wit at *
  intro st Q h hn
  cases h with
  | letIn he hb _ => cases he with | litU hv => exact next _ Q (hb _ _ hv) hn

#print axioms letIn_inv
#print axioms step_seq
#print axioms step_fn
#print axioms step_var
#print axioms step_constU
#print axioms pure_inv
#print axioms step_fEq
#print axioms step_uLeq
#print axioms step_assert
#print axioms step_mkArray1
#print axioms step_cast
#print axioms step_decl
#print axioms step_call
#print axioms wit_letIn
#print axioms wit_pure
#print axioms wit_cast
#print axioms wit_constU
#print axioms wit_litU
#print axioms wit_skip
#print axioms wit_call
#print axioms Wit.run
#print axioms wit_let_pure
#print axioms wit_let_cast
#print axioms wit_let_constU
#print axioms wit_let_litU
end Deposit.Rules
