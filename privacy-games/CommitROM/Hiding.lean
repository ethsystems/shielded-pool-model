import CommitROM.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}

structure Adversary (M S C : Type) {I : Type} (aux : OracleSpec I) where
  State : Type
  choose : OracleComp (attackSpec M S C aux) (M × M × State)
  guess : State → C → OracleComp (attackSpec M S C aux) Bool

def QueryBound (adv : Adversary M S C aux) (qc qg : Nat) : Prop :=
  adv.choose.IsQueryBoundP (charged (C := C) (aux := aux)) qc ∧
    ∀ state cm, (adv.guess state cm).IsQueryBoundP (charged (C := C) (aux := aux)) qg

noncomputable def test (adv : Adversary M S C aux) (f : M → C) :
    OracleComp (attackSpec M S C aux) Bool := do
  let (ml,mr,state) ← adv.choose
  let b ← liftComp ($ᵗ Bool) (attackSpec M S C aux)
  let g ← adv.guess state (f (if b then mr else ml))
  pure (b == g)

theorem coins_bound {α : Type} (oa : ProbComp α) (q : Nat) :
    (liftComp oa (attackSpec M S C aux)).IsQueryBoundP (charged (C := C) (aux := aux)) q := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind]
    change IsQueryBoundP (liftM ((attackSpec M S C aux).query (.inl t)) >>=
      fun u => liftComp (k u) (attackSpec M S C aux)) (charged (C := C) (aux := aux)) q
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [charged]), fun u => by simpa [charged] using ih u⟩

theorem test_bound (adv : Adversary M S C aux) (qc qg : Nat)
    (hq : QueryBound adv qc qg) (f : M → C) :
    (test adv f).IsQueryBoundP (charged (C := C) (aux := aux)) (qc+qg) := by
  unfold test
  apply isQueryBoundP_bind hq.1
  intro x _
  refine (isQueryBoundP_bind (n := 0) (m := qg) (coins_bound _ 0) ?_).mono (by simp)
  intro b _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using hq.2 x.2.2 _

theorem run_coins {α : Type} (other : QueryImpl aux Id) (h : M × S → C) (oa : ProbComp α) :
    run other h (liftComp oa (attackSpec M S C aux)) = oa := by
  unfold run
  rw [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_toQueryImpl]

variable [Finite M] [Fintype S] [Finite C] [Nonempty C]
  [SampleableType S] [SampleableType C]
  [SampleableType (M × S → C)] [SampleableType (M → C)]

noncomputable def experiment (other : QueryImpl aux Id) (adv : Adversary M S C aux) : ProbComp Bool :=
  real other (test adv)

noncomputable def advantage (other : QueryImpl aux Id) (adv : Adversary M S C aux) : ℝ :=
  |(Pr[= true | experiment other adv]).toReal - 1/2|

theorem uniform_eval_bind {X : Type} (m : M) (k : C → ProbComp X) :
    𝒮[do let f ← $ᵗ (M → C); k (f m)] = 𝒮[($ᵗ C) >>= k] := by
  have he := WithdrawGame.ROM.uniform_eval (K := C) m
  have hh : (do let f ← $ᵗ (M → C); k (f m)) =
      ((fun f : M → C => f m) <$> ($ᵗ (M → C))) >>= k := by simp
  rw [hh, evalSPMF_bind, he, ← evalSPMF_bind]

theorem ideal_fair (other : QueryImpl aux Id) (adv : Adversary M S C aux) :
    Pr[= true | ideal other (test adv)] = 1/2 := by
  have he : 𝒮[ideal other (test adv)] = 𝒮[do
      let h ← $ᵗ (M × S → C)
      let x ← run other h adv.choose
      let cm ← $ᵗ C
      let g ← run other h (adv.guess x.2.2 cm)
      let b ← $ᵗ Bool
      pure (b == g)] := by
    unfold ideal test
    simp only [run, simulateQ_bind, simulateQ_pure]
    apply evalSPMF_bind_congr_left
    intro h
    rw [evalSPMF_bind_comm ($ᵗ (M → C))]
    apply evalSPMF_bind_congr_left
    intro x
    have hc := run_coins other h ($ᵗ Bool)
    unfold run at hc
    rw [hc]
    rw [evalSPMF_bind_comm ($ᵗ (M → C))]
    calc
      _ = 𝒮[do
        let b ← $ᵗ Bool
        let cm ← $ᵗ C
        let g ← run other h (adv.guess x.2.2 cm)
        pure (b == g)] := by
          apply evalSPMF_bind_congr_left
          intro b
          exact uniform_eval_bind (C := C) (if b then x.2.1 else x.1)
            (fun cm => do let g ← run other h (adv.guess x.2.2 cm); pure (b == g))
      _ = _ := by
        rw [evalSPMF_bind_comm ($ᵗ Bool)]
        apply evalSPMF_bind_congr_left
        intro cm
        rw [evalSPMF_bind_comm ($ᵗ Bool)]
        rfl
  rw [probOutput_congr (x := true) rfl he]
  have hb (g : Bool) : Pr[= true | do let b ← $ᵗ Bool; pure (b == g)] = 1/2 := by
    cases g <;> simp
  simp only [probOutput_bind_eq_tsum] at hb ⊢
  simp_rw [hb]
  simp only [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/-- Adaptive messages and both attacker phases are covered. The salt stays private. -/
theorem advantage_le_queryBound (other : QueryImpl aux Id) (adv : Adversary M S C aux)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage other adv ≤ (qc + qg : ℝ) / Fintype.card S := by
  have h := switch_bound other (test adv) (qc+qg) (test_bound adv qc qg hq)
  simpa [advantage, experiment, ProbComp.boolDistAdvantage, ideal_fair, Nat.cast_add] using h

end LeanShieldedPool.CommitROM
