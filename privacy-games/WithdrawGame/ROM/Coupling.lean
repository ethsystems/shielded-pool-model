import WithdrawGame.ROM.Program

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
noncomputable local instance (priority := 100000) couplingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {P : PrimSpec}

def Avoid (S : Set P.SpendKey) (xs : List P.SpendKey) : Prop :=
  ∀ k ∈ xs, k ∉ S

theorem trace_eq_good {α : Type} (S : Set P.SpendKey)
    (so so' : QueryImpl (attackSpec P) ProbComp)
    (agree : ∀ t, Avoid S (queryKeys P t) → so t = so' t)
    (oa : OracleComp (attackSpec P) α) (z : α × List P.SpendKey)
    (hz : Avoid S z.2) : Pr[= z | trace so oa] = Pr[= z | trace so' oa] := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x => rfl
  | query_bind t k ih =>
    rw [trace_query_bind, trace_query_bind]
    simp only [probOutput_bind_eq_tsum]
    by_cases ht : Avoid S (queryKeys P t)
    · rw [agree t ht]
      apply tsum_congr
      intro u
      congr 1
      apply tsum_congr
      intro w
      by_cases hw : z = (w.1, queryKeys P t ++ w.2)
      · have hwgood : Avoid S w.2 := by
          intro x hx
          apply hz x
          rw [hw]
          exact List.mem_append_right _ hx
        rw [ih u w hwgood]
      · simp [probOutput_pure, hw]
    · have hzero (w : α × List P.SpendKey) : z ≠ (w.1, queryKeys P t ++ w.2) := by
        intro he
        apply ht
        intro x hx
        apply hz x
        rw [he]
        exact List.mem_append_left _ hx
      simp [probOutput_pure, hzero]

/-- Equal good traces imply equal bad mass, since both runs terminate. -/
theorem trace_bad_eq {α : Type} (S : Set P.SpendKey)
    (so so' : QueryImpl (attackSpec P) ProbComp)
    (agree : ∀ t, Avoid S (queryKeys P t) → so t = so' t)
    (oa : OracleComp (attackSpec P) α) :
    Pr[fun z => ¬Avoid S z.2 | trace so oa] =
      Pr[fun z => ¬Avoid S z.2 | trace so' oa] := by
  have hg : Pr[fun z => Avoid S z.2 | trace so oa] =
      Pr[fun z => Avoid S z.2 | trace so' oa] := by
    simp only [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro z
    by_cases hz : Avoid S z.2
    · simp [hz, trace_eq_good S so so' agree oa z hz]
    · simp [hz]
  have h₁ := probEvent_compl (trace so oa) (fun z => Avoid S z.2)
  have h₂ := probEvent_compl (trace so' oa) (fun z => Avoid S z.2)
  rw [hg] at h₁
  simp only [probFailure_eq_zero, tsub_zero] at h₁ h₂
  exact (ENNReal.add_right_inj (by finiteness)).mp (h₁.trans h₂.symm)

/-- Fundamental lemma for eager oracles with an actual attacker query trace. -/
theorem distance_le_trace_hit (S : Set P.SpendKey)
    (so so' : QueryImpl (attackSpec P) ProbComp)
    (agree : ∀ t, Avoid S (queryKeys P t) → so t = so' t)
    (oa : OracleComp (attackSpec P) Bool) :
    (simulateQ so oa).boolDistAdvantage (simulateQ so' oa) ≤
      (Pr[fun z => ¬Avoid S z.2 | trace so oa]).toReal := by
  have ht := tvDist_le_probEvent_of_probOutput_eq_of_not
    (mx := trace so oa) (my := trace so' oa) (fun z => ¬Avoid S z.2)
    (fun z hz => trace_eq_good S so so' agree oa z (not_not.mp hz))
    (trace_bad_eq S so so' agree oa)
  have hm := tvDist_map_le (m := ProbComp) Prod.fst (trace so oa) (trace so' oa)
  simp only [trace, QueryImpl.fst_map_run_withTraceAppendBefore] at hm
  exact (abs_probOutput_toReal_sub_le_tvDist (simulateQ so oa) (simulateQ so' oa)).trans
    (hm.trans ht)

theorem distance_bind_le_bad {A B : Type} [Fintype A]
    (d : ProbComp A) (f g : A → ProbComp Bool) (bad : A → ProbComp B) (p : B → Prop)
    (h : ∀ a, (f a).boolDistAdvantage (g a) ≤ (Pr[p | bad a]).toReal) :
    (d >>= f).boolDistAdvantage (d >>= g) ≤ (Pr[p | d >>= bad]).toReal := by
  refine (PoolGame.Averaging.boolDistAdvantage_bind_le d f g).trans ?_
  rw [tsum_fintype, probEvent_bind_eq_tsum, tsum_fintype,
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  simp only [ENNReal.toReal_mul]
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

end LeanShieldedPool.WithdrawGame.ROM
