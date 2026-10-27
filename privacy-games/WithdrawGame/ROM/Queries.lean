import WithdrawGame.ROM.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.ROM
variable {P : PrimSpec} {ι : Type}

def queryKeys (P : PrimSpec) : (attackSpec P).Domain → List P.SpendKey
  | .inl _ => []
  | .inr (.inl k) => [k]
  | .inr (.inr (k, _)) => [k]

def trace {α : Type} (so : QueryImpl (attackSpec P) ProbComp)
    (oa : OracleComp (attackSpec P) α) : ProbComp (α × List P.SpendKey) :=
  (simulateQ (so.withTraceAppendBefore (queryKeys P)) oa).run

theorem trace_query_bind {α : Type} (so : QueryImpl (attackSpec P) ProbComp)
    (t : (attackSpec P).Domain) (k : (attackSpec P).Range t → OracleComp (attackSpec P) α) :
    trace so (liftM ((attackSpec P).query t) >>= k) = (do
      let u ← so t
      let z ← trace so (k u)
      pure (z.1, queryKeys P t ++ z.2)) := by
  simp [trace, WriterT.run_tell, bind_assoc]

/-- The VCV query bound controls the actual trace. Random coins add no key probes. -/
theorem trace_length_bound {α : Type} (so : QueryImpl (attackSpec P) ProbComp)
    (oa : OracleComp (attackSpec P) α) (q : Nat)
    (h : oa.IsQueryBoundP (charged P) q) :
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
    | inl coin => simpa [queryKeys, charged] using hi
    | inr hash =>
      have hp : 0 < q := h.1.resolve_left (by simp [charged])
      cases hash <;> simp [queryKeys, charged] at hi ⊢ <;> omega

/-- An independent uniform key hits a fixed transcript with probability at most length / |K|. -/
theorem uniform_key_mem_list {K : Type} [Fintype K] [SampleableType K] (xs : List K) :
    Pr[fun k => k ∈ xs | $ᵗ K] ≤ (xs.length : ℝ≥0∞) / Fintype.card K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := probEvent_or_le ($ᵗ K) (fun k => k = x) (fun k => k ∈ xs)
    simp only [List.mem_cons] at *
    have hx : Pr[fun k => k = x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := by simp
    rw [hx] at h
    calc
      _ ≤ (Fintype.card K : ℝ≥0∞)⁻¹ + Pr[fun k => k ∈ xs | $ᵗ K] := h
      _ ≤ (Fintype.card K : ℝ≥0∞)⁻¹ + (xs.length : ℝ≥0∞) / Fintype.card K := by gcongr
      _ = _ := by simp [List.length_cons, Nat.cast_add, div_eq_mul_inv, add_mul, add_comm]

/-- This bound requires an independent target key. Applying it to the real ROM transcript
needs the unproved OracleSwitch reduction; public keys and logs cannot be ignored. -/
theorem independent_trace_key_hit_bound [Fintype P.SpendKey] [SampleableType P.SpendKey]
    {α : Type} (so : QueryImpl (attackSpec P) ProbComp)
    (oa : OracleComp (attackSpec P) α) (q : Nat)
    (h : oa.IsQueryBoundP (charged P) q) :
    Pr[fun z : (α × List P.SpendKey) × P.SpendKey => z.2 ∈ z.1.2 | do
      let z ← trace so oa
      let k ← $ᵗ P.SpendKey
      pure (z, k)] ≤ (q : ℝ≥0∞) / Fintype.card P.SpendKey := by
  rw [probEvent_bind_eq_tsum]
  have ht (z : α × List P.SpendKey) (hz : z ∈ support (trace so oa)) :
      Pr[fun w : (α × List P.SpendKey) × P.SpendKey => w.2 ∈ w.1.2 | do
        let k ← $ᵗ P.SpendKey
        pure (z, k)] ≤ (q : ℝ≥0∞) / Fintype.card P.SpendKey := by
    have hk := uniform_key_mem_list (K := P.SpendKey) z.2
    have hl := trace_length_bound so oa q h z hz
    calc
      _ = Pr[fun k => k ∈ z.2 | $ᵗ P.SpendKey] := by simp [Function.comp_def]
      _ ≤ (z.2.length : ℝ≥0∞) / Fintype.card P.SpendKey := hk
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑' z, Pr[= z | trace so oa] * ((q : ℝ≥0∞) / Fintype.card P.SpendKey) := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : z ∈ support (trace so oa)
      · gcongr; exact ht z hz
      · simp [probOutput_eq_zero_of_not_mem_support hz]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

end LeanShieldedPool.WithdrawGame.ROM
