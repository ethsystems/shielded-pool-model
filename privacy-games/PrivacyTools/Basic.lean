import OwnerGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.PrivacyTools
variable {P : PrimSpec} {ι : Type}

noncomputable def coin (f : Bool → ProbComp Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let g ← f b
  pure (b == g)

theorem coin_bias (f : Bool → ProbComp Bool) :
    |(Pr[= true | coin f]).toReal - 1/2| = (f true).boolDistAdvantage (f false) / 2 := by
  have h := ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
    (pure () : ProbComp Unit) (fun _ => f true) (fun _ => f false)
  have he (b : Bool) :
      (if b then (do let z ← f true; pure (b == z))
       else (do let z ← f false; pure (b == z))) =
      (do let z ← f b; pure (b == z) : ProbComp Bool) := by cases b <;> rfl
  simp only [pure_bind, he, ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half] at h
  unfold coin
  linarith

theorem distance_fair (p : ProbComp Bool) :
    p.boolDistAdvantage ($ᵗ Bool) = |(Pr[= true | p]).toReal - 1/2| := by
  norm_num [ProbComp.boolDistAdvantage]

/-- A two-output hybrid. Epsilon is the distance allowance for one commitment. -/
theorem hiding_pair [SampleableType P.Salt] (ε : ℝ) (h : OwnerGame.Hiding (P := P) ε)
    (t₁ t₂ t₁' t₂' : P.Token) (a₁ a₂ a₁' a₂' : Nat)
    (pk₁ pk₂ pk₁' pk₂' : P.PubKey) (test : P.Commitment → P.Commitment → ProbComp Bool) :
    (do let s₁ ← $ᵗ P.Salt; let s₂ ← $ᵗ P.Salt
        test (P.commit t₁ a₁ pk₁ s₁) (P.commit t₂ a₂ pk₂ s₂)).boolDistAdvantage
    (do let s₁ ← $ᵗ P.Salt; let s₂ ← $ᵗ P.Salt
        test (P.commit t₁' a₁' pk₁' s₁) (P.commit t₂' a₂' pk₂' s₂)) ≤ 2 * ε := by
  let middle : ProbComp Bool := do
    let s₁ ← $ᵗ P.Salt
    let s₂ ← $ᵗ P.Salt
    test (P.commit t₁' a₁' pk₁' s₁) (P.commit t₂ a₂ pk₂ s₂)
  have h₁ := h t₁ a₁ pk₁ t₁' a₁' pk₁' (fun cm => do
    let s₂ ← $ᵗ P.Salt
    test cm (P.commit t₂ a₂ pk₂ s₂))
  have h₂ := PoolGame.Averaging.boolDistAdvantage_bind_le_const ($ᵗ P.Salt)
    (fun s₁ => do let s₂ ← $ᵗ P.Salt; test (P.commit t₁' a₁' pk₁' s₁) (P.commit t₂ a₂ pk₂ s₂))
    (fun s₁ => do let s₂ ← $ᵗ P.Salt; test (P.commit t₁' a₁' pk₁' s₁) (P.commit t₂' a₂' pk₂' s₂)) ε
    (fun s₁ _ => h t₂ a₂ pk₂ t₂' a₂' pk₂' (test (P.commit t₁' a₁' pk₁' s₁)))
  exact (ProbComp.boolDistAdvantage_triangle _ middle _).trans (by linarith)


theorem pure_or_fair_probability {α : Type} (d : ProbComp α) (p : α → Prop) [DecidablePred p] :
    (Pr[= true | do let a ← d; if p a then pure true else $ᵗ Bool]).toReal =
      1/2 + (Pr[p | d]).toReal / 2 := by
  have he : Pr[= true | do let a ← d; if p a then pure true else $ᵗ Bool] =
      Pr[p | d] + Pr[fun a => ¬p a | d] * (1/2) := by
    simp only [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases h : p a <;> simp [h]
  rw [he, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
  have hc := congrArg ENNReal.toReal (probEvent_compl d p)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hc
  norm_num at hc ⊢
  linarith

theorem independent_and {α β : Type} (d : ProbComp α) (e : ProbComp β)
    (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    Pr[= true | do let a ← d; let b ← e; pure (decide (p a ∧ q b))] =
      Pr[p | d] * Pr[q | e] := by
  have hi (a : α) : Pr[= true | do let b ← e; pure (decide (p a ∧ q b))] =
      if p a then Pr[q | e] else 0 := by
    by_cases h : p a
    · simp only [h, true_and, if_true]
      simp [← probEvent_eq_eq_probOutput, Function.comp_def]
    · simp [h]
  rw [probOutput_bind_eq_tsum]
  simp only [hi]
  have hf (a : α) : Pr[= a | d] * (if p a then Pr[q | e] else 0) =
      (if p a then Pr[= a | d] else 0) * Pr[q | e] := by
    by_cases h : p a <;> simp [h]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right]
  simp only [probEvent_eq_tsum_ite]

end LeanShieldedPool.PrivacyTools
