import WithdrawGame.ROM.Reduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}

abbrev attackSpec (M S C : Type) {I : Type} (aux : OracleSpec I) :=
  unifSpec + (((M × S) →ₒ C) + aux)

def charged : (attackSpec M S C aux).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance chargedDecidable : DecidablePred (charged (M := M) (S := S) (C := C) (aux := aux)) :=
  fun t => match t with
  | .inl _ => isFalse (fun h => h)
  | .inr _ => isTrue trivial

attribute [local instance 200000] chargedDecidable

def querySalts : (attackSpec M S C aux).Domain → List S
  | .inr (.inl x) => [x.2]
  | _ => []

def run {α : Type} (other : QueryImpl aux Id) (h : M × S → C)
    (oa : OracleComp (attackSpec M S C aux) α) : ProbComp α :=
  simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn h + other)) oa

def trace {α : Type} (so : QueryImpl (attackSpec M S C aux) ProbComp)
    (oa : OracleComp (attackSpec M S C aux) α) : ProbComp (α × List S) :=
  (simulateQ (so.withTraceAppendBefore querySalts) oa).run

theorem trace_query_bind {α : Type} (so : QueryImpl (attackSpec M S C aux) ProbComp)
    (t : (attackSpec M S C aux).Domain)
    (k : (attackSpec M S C aux).Range t → OracleComp (attackSpec M S C aux) α) :
    trace so (liftM ((attackSpec M S C aux).query t) >>= k) = (do
      let u ← so t
      let z ← trace so (k u)
      pure (z.1, querySalts t ++ z.2)) := by
  simp [trace, WriterT.run_tell, bind_assoc]

theorem trace_length_bound {α : Type} (so : QueryImpl (attackSpec M S C aux) ProbComp)
    (oa : OracleComp (attackSpec M S C aux) α) (q : Nat)
    (h : oa.IsQueryBoundP (charged (C := C) (aux := aux)) q) :
    ∀ z ∈ support (trace so oa), z.2.length ≤ q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x => simp [trace]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    intro z hz
    rw [trace_query_bind] at hz
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, _, z', hz', rfl⟩ := hz
    have hi := ih u _ (h.2 u) z' hz'
    cases t with
    | inl coin => simpa [querySalts, charged] using hi
    | inr hash =>
      have hp : 0 < q := h.1.resolve_left (by simp [charged])
      cases hash <;> simp [querySalts, charged] at hi ⊢ <;> omega

noncomputable local instance (priority := 100000) classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def Avoid (bad : Set S) (xs : List S) : Prop :=
  ∀ k ∈ xs, k ∉ bad

theorem trace_eq_good {α : Type} (bad : Set S)
    (so so' : QueryImpl (attackSpec M S C aux) ProbComp)
    (agree : ∀ t, Avoid bad (querySalts t) → so t = so' t)
    (oa : OracleComp (attackSpec M S C aux) α) (z : α × List S)
    (hz : Avoid bad z.2) : Pr[= z | trace so oa] = Pr[= z | trace so' oa] := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x => rfl
  | query_bind t k ih =>
    rw [trace_query_bind, trace_query_bind]
    simp only [probOutput_bind_eq_tsum]
    by_cases ht : Avoid bad (querySalts t)
    · rw [agree t ht]
      apply tsum_congr
      intro u
      congr 1
      apply tsum_congr
      intro w
      by_cases hw : z = (w.1, querySalts t ++ w.2)
      · have hwgood : Avoid bad w.2 := by
          intro x hx
          apply hz x
          rw [hw]
          exact List.mem_append_right _ hx
        rw [ih u w hwgood]
      · simp [probOutput_pure, hw]
    · have hzero (w : α × List S) : z ≠ (w.1, querySalts t ++ w.2) := by
        intro he
        apply ht
        intro x hx
        apply hz x
        rw [he]
        exact List.mem_append_left _ hx
      simp [probOutput_pure, hzero]

/-- Equal good traces imply equal bad mass, since both runs terminate. -/
theorem trace_bad_eq {α : Type} (bad : Set S)
    (so so' : QueryImpl (attackSpec M S C aux) ProbComp)
    (agree : ∀ t, Avoid bad (querySalts t) → so t = so' t)
    (oa : OracleComp (attackSpec M S C aux) α) :
    Pr[fun z => ¬Avoid bad z.2 | trace so oa] =
      Pr[fun z => ¬Avoid bad z.2 | trace so' oa] := by
  have hg : Pr[fun z => Avoid bad z.2 | trace so oa] =
      Pr[fun z => Avoid bad z.2 | trace so' oa] := by
    simp only [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro z
    by_cases hz : Avoid bad z.2
    · simp [hz, trace_eq_good bad so so' agree oa z hz]
    · simp [hz]
  have h₁ := probEvent_compl (trace so oa) (fun z => Avoid bad z.2)
  have h₂ := probEvent_compl (trace so' oa) (fun z => Avoid bad z.2)
  rw [hg] at h₁
  simp only [probFailure_eq_zero, tsub_zero] at h₁ h₂
  exact (ENNReal.add_right_inj (by finiteness)).mp (h₁.trans h₂.symm)

/-- Fundamental lemma for eager oracles with an actual attacker query trace. -/
theorem distance_le_trace_hit (bad : Set S)
    (so so' : QueryImpl (attackSpec M S C aux) ProbComp)
    (agree : ∀ t, Avoid bad (querySalts t) → so t = so' t)
    (oa : OracleComp (attackSpec M S C aux) Bool) :
    (simulateQ so oa).boolDistAdvantage (simulateQ so' oa) ≤
      (Pr[fun z => ¬Avoid bad z.2 | trace so oa]).toReal := by
  have ht := tvDist_le_probEvent_of_probOutput_eq_of_not
    (mx := trace so oa) (my := trace so' oa) (fun z => ¬Avoid bad z.2)
    (fun z hz => trace_eq_good bad so so' agree oa z (not_not.mp hz))
    (trace_bad_eq bad so so' agree oa)
  have hm := tvDist_map_le (m := ProbComp) Prod.fst (trace so oa) (trace so' oa)
  simp only [trace, QueryImpl.fst_map_run_withTraceAppendBefore] at hm
  exact (abs_probOutput_toReal_sub_le_tvDist (simulateQ so oa) (simulateQ so' oa)).trans
    (hm.trans ht)

theorem independent_trace_hit [Fintype S] [SampleableType S] {α : Type}
    (so : QueryImpl (attackSpec M S C aux) ProbComp)
    (oa : OracleComp (attackSpec M S C aux) α) (q : Nat)
    (hq : oa.IsQueryBoundP (charged (C := C) (aux := aux)) q) :
    Pr[fun z : (α × List S) × S => z.2 ∈ z.1.2 | do
      let z ← trace so oa; let s ← $ᵗ S; pure (z,s)] ≤ (q : ℝ≥0∞) / Fintype.card S := by
  apply probEvent_bind_le_of_forall_le
  intro z hz
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  exact (WithdrawGame.ROM.uniform_key_mem_list z.2).trans (by
    gcongr
    exact trace_length_bound so oa q hq z hz)

def saltCoord (s : S) (m : M) : M × S := (m,s)

theorem saltCoord_injective (s : S) : Function.Injective (saltCoord (M := M) s) := by
  intro x y h
  exact congrArg Prod.fst h

theorem program_answers_agree (other : QueryImpl aux Id) (h : M × S → C)
    (f : M → C) (s : S) (t : (attackSpec M S C aux).Domain)
    (ht : Avoid {s} (querySalts t)) :
    unifFwdAnswerImpl (QueryImpl.ofFn h + other) t =
      unifFwdAnswerImpl (QueryImpl.ofFn (WithdrawGame.ROM.program (saltCoord s) h f) + other) t := by
  cases t with
  | inl coin => rfl
  | inr hash =>
    cases hash with
    | inr x => rfl
    | inl x =>
      have hs : x.2 ≠ s := ht x.2 (by simp [querySalts])
      change pure (h x) = (pure (WithdrawGame.ROM.program (saltCoord s) h f x) : ProbComp C)
      rw [WithdrawGame.ROM.program_outside]
      rintro ⟨m,hm⟩
      exact hs (congrArg Prod.snd hm).symm

theorem programming_bound [Fintype S] [SampleableType S]
    (other : QueryImpl aux Id) (h : M × S → C) (f : M → C)
    (oa : OracleComp (attackSpec M S C aux) Bool) (q : Nat)
    (hq : oa.IsQueryBoundP (charged (C := C) (aux := aux)) q) :
    (do let _s ← $ᵗ S; run other h oa).boolDistAdvantage
      (do let s ← $ᵗ S; run other (WithdrawGame.ROM.program (saltCoord s) h f) oa) ≤
        (q : ℝ) / Fintype.card S := by
  let so := unifFwdAnswerImpl (QueryImpl.ofFn h + other)
  have hd := WithdrawGame.ROM.distance_bind_le_bad ($ᵗ S)
    (fun _ => run other h oa)
    (fun s => run other (WithdrawGame.ROM.program (saltCoord s) h f) oa)
    (fun s => do let z ← trace so oa; pure (z,s))
    (fun z => z.2 ∈ z.1.2) (fun s => by
      have ht := distance_le_trace_hit {s} so
        (unifFwdAnswerImpl (QueryImpl.ofFn (WithdrawGame.ROM.program (saltCoord s) h f) + other))
        (program_answers_agree other h f s) oa
      simpa [bind_pure_comp, probEvent_map, Function.comp_def, Avoid, run, so] using ht)
  have he : Pr[fun z : (Bool × List S) × S => z.2 ∈ z.1.2 |
      do let s ← $ᵗ S; let z ← trace so oa; pure (z,s)] =
      Pr[fun z => z.2 ∈ z.1.2 |
      do let z ← trace so oa; let s ← $ᵗ S; pure (z,s)] := by
    simp only [probEvent_def]
    rw [evalSPMF_bind_comm]
  rw [he] at hd
  have hb := ENNReal.toReal_mono (by finiteness) (independent_trace_hit so oa q hq)
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hb
  exact hd.trans hb

end LeanShieldedPool.CommitROM
