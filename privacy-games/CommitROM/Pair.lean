import CommitROM.Hiding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}

structure PairAdversary (M S C : Type) {I : Type} (aux : OracleSpec I) where
  State : Type
  choose : OracleComp (attackSpec M S C aux) ((M × M) × (M × M) × State)
  guess : State → C → C → OracleComp (attackSpec M S C aux) Bool

def PairQueryBound (adv : PairAdversary M S C aux) (qc qg : Nat) : Prop :=
  adv.choose.IsQueryBoundP (charged (C := C) (aux := aux)) qc ∧
    ∀ state c₁ c₂, (adv.guess state c₁ c₂).IsQueryBoundP (charged (C := C) (aux := aux)) qg

noncomputable def pairTest [SampleableType S] (adv : PairAdversary M S C aux) (f : M → C) :
    OracleComp (attackSpec M S C aux) Bool := do
  let x ← adv.choose
  let b ← liftComp ($ᵗ Bool) (attackSpec M S C aux)
  let s₂ ← liftComp ($ᵗ S) (attackSpec M S C aux)
  let c₂ ← liftM ((attackSpec M S C aux).query (.inr (.inl ((if b then x.2.1.2 else x.2.1.1),s₂))))
  let g ← adv.guess x.2.2 (f (if b then x.1.2 else x.1.1)) c₂
  pure (b == g)

theorem pairTest_bound [SampleableType S] (adv : PairAdversary M S C aux)
    (qc qg : Nat) (hq : PairQueryBound adv qc qg) (f : M → C) :
    (pairTest adv f).IsQueryBoundP (charged (C := C) (aux := aux)) (qc + (1+qg)) := by
  unfold pairTest
  apply isQueryBoundP_bind hq.1
  intro x _
  apply (isQueryBoundP_bind (n := 0) (m := 1+qg) (coins_bound _ 0) ?_).mono (by simp)
  intro b _
  apply (isQueryBoundP_bind (n := 0) (m := 1+qg) (coins_bound _ 0) ?_).mono (by simp)
  intro s₂ _
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · exact Or.inr (by omega)
  · intro c₂
    simpa [charged, bind_pure_comp, isQueryBoundP_map_iff] using hq.2 x.2.2 _ c₂

noncomputable def secondReduction [SampleableType C] (adv : PairAdversary M S C aux) :
    Adversary M S C aux where
  State := adv.State × C
  choose := do
    let x ← adv.choose
    let c₁ ← liftComp ($ᵗ C) (attackSpec M S C aux)
    pure (x.2.1.1,x.2.1.2,(x.2.2,c₁))
  guess := fun s c₂ => adv.guess s.1 s.2 c₂

theorem secondReduction_bound [SampleableType C] (adv : PairAdversary M S C aux)
    (qc qg : Nat) (hq : PairQueryBound adv qc qg) :
    QueryBound (secondReduction adv) qc qg := by
  unfold QueryBound secondReduction
  constructor
  · apply (isQueryBoundP_bind (n := qc) (m := 0) hq.1 ?_).mono (by simp)
    intro x _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      (coins_bound (M := M) (S := S) (aux := aux) ($ᵗ C) 0)
  · intro s c₂
    exact hq.2 _ _ _

variable [Finite M] [Fintype S] [Finite C] [Nonempty C]
  [SampleableType S] [SampleableType C]
  [SampleableType (M × S → C)] [SampleableType (M → C)]

noncomputable def pairExperiment (other : QueryImpl aux Id) (adv : PairAdversary M S C aux) : ProbComp Bool := do
  let h ← $ᵗ (M × S → C)
  let x ← run other h adv.choose
  let s₁ ← $ᵗ S
  let s₂ ← $ᵗ S
  let b ← $ᵗ Bool
  let g ← run other h (adv.guess x.2.2
    (h ((if b then x.1.2 else x.1.1),s₁))
    (h ((if b then x.2.1.2 else x.2.1.1),s₂)))
  pure (b == g)

theorem pair_real_eq (other : QueryImpl aux Id) (adv : PairAdversary M S C aux) :
    𝒮[real other (pairTest adv)] = 𝒮[pairExperiment other adv] := by
  unfold real pairExperiment pairTest
  rw [evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left
  intro h
  simp only [run, simulateQ_bind, simulateQ_pure]
  rw [evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left
  intro x
  apply evalSPMF_bind_congr_left
  intro s₁
  have hb := run_coins other h ($ᵗ Bool)
  have hs := run_coins other h ($ᵗ S)
  unfold run at hb hs
  rw [hb, hs, evalSPMF_bind_comm ($ᵗ Bool)]
  apply evalSPMF_bind_congr_left
  intro s₂
  apply evalSPMF_bind_congr_left
  intro b
  simp only [simulateQ_query]
  change 𝒮[(pure (h ((if b then x.2.1.2 else x.2.1.1),s₂)) : ProbComp C) >>= _] = _
  rw [pure_bind]
  rfl

theorem pair_ideal_eq_second (other : QueryImpl aux Id) (adv : PairAdversary M S C aux) :
    𝒮[ideal other (pairTest adv)] = 𝒮[experiment other (secondReduction adv)] := by
  unfold ideal pairTest experiment real test secondReduction
  rw [evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left
  intro h
  simp only [run, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  rw [evalSPMF_bind_comm ($ᵗ (M → C)), evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left
  intro x
  have hb := run_coins other h ($ᵗ Bool)
  have hs := run_coins other h ($ᵗ S)
  have hc := run_coins other h ($ᵗ C)
  unfold run at hb hs hc
  rw [hb, hs, hc]
  rw [evalSPMF_bind_comm ($ᵗ (M → C))]
  calc
    _ = 𝒮[do
      let b ← $ᵗ Bool
      let c₁ ← $ᵗ C
      let s₂ ← $ᵗ S
      let g ← run other h (adv.guess x.2.2 c₁ (h ((if b then x.2.1.2 else x.2.1.1),s₂)))
      pure (b == g)] := by
        apply evalSPMF_bind_congr_left
        intro b
        have hu := uniform_eval_bind (C := C) (if b then x.1.2 else x.1.1)
          (fun c₁ => do
            let s₂ ← $ᵗ S
            let g ← run other h (adv.guess x.2.2 c₁ (h ((if b then x.2.1.2 else x.2.1.1),s₂)))
            pure (b == g))
        convert hu using 1
        apply evalSPMF_bind_congr_left
        intro f
        apply evalSPMF_bind_congr_left
        intro s₂
        simp only [simulateQ_query]
        change 𝒮[(pure (h ((if b then x.2.1.2 else x.2.1.1),s₂)) : ProbComp C) >>= _] = _
        rw [pure_bind]
        rfl
    _ = _ := by
      rw [evalSPMF_bind_comm ($ᵗ Bool)]
      rw [evalSPMF_bind_comm ($ᵗ S)]
      apply evalSPMF_bind_congr_left
      intro c₁
      rw [evalSPMF_bind_comm ($ᵗ Bool)]
      rfl

/-- Two fresh salts share one oracle; the extra unit covers cross-output salt collision. -/
theorem pair_advantage_le_queryBound (other : QueryImpl aux Id) (adv : PairAdversary M S C aux)
    (qc qg : Nat) (hq : PairQueryBound adv qc qg) :
    |(Pr[= true | pairExperiment other adv]).toReal - 1/2| ≤
      (2*(qc+qg)+1 : ℝ) / Fintype.card S := by
  have hs := switch_bound other (pairTest adv) (qc+(1+qg)) (pairTest_bound adv qc qg hq)
  unfold ProbComp.boolDistAdvantage at hs
  rw [probOutput_congr (x := true) rfl (pair_real_eq other adv),
    probOutput_congr (x := true) rfl (pair_ideal_eq_second other adv)] at hs
  have hi := advantage_le_queryBound other (secondReduction adv) qc qg (secondReduction_bound adv qc qg hq)
  unfold advantage at hi
  have ht := abs_sub_le (Pr[= true | pairExperiment other adv]).toReal
    (Pr[= true | experiment other (secondReduction adv)]).toReal (1/2)
  push_cast at hs
  have he : ((qc : ℝ)+(1+qg)) / Fintype.card S + (qc+qg : ℝ) / Fintype.card S =
      (2*(qc+qg)+1 : ℝ) / Fintype.card S := by ring
  linarith

end LeanShieldedPool.CommitROM
