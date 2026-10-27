import WithdrawGame.ROM.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
noncomputable local instance (priority := 100000) badDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- One coordinate of an independently sampled key map is uniform. -/
theorem uniform_eval {I K : Type} [Finite I] [Finite K] [Nonempty K]
    [SampleableType K] [SampleableType (I → K)] (i : I) :
    𝒮[(fun keys : I → K => keys i) <$> ($ᵗ (I → K))] = 𝒮[$ᵗ K] := by
  classical
  have h := congrArg (Functor.map (f := SPMF) (fun keys : I → K => keys i))
    (evalSPMF_uniformSample_bind_update (R := K) i)
  rw [← evalSPMF_map, ← evalSPMF_map] at h
  simp only [map_bind, map_pure, Function.update_self] at h
  rw [← h]
  apply evalSPMF_ext
  intro k
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  simp

theorem keymap_hit_list {I K : Type} [Fintype I] [Fintype K] [Nonempty K]
    [SampleableType K] [SampleableType (I → K)] (xs : List K) :
    Pr[fun keys : I → K => ∃ i, keys i ∈ xs | $ᵗ (I → K)] ≤
      (Fintype.card I : ℝ≥0∞) * xs.length / Fintype.card K := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset I) ($ᵗ (I → K))
    (fun i keys => keys i ∈ xs)
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ?_
  calc
    _ ≤ ∑ _i : I, (xs.length : ℝ≥0∞) / Fintype.card K := by
      apply Finset.sum_le_sum
      intro i _
      have he : Pr[fun keys : I → K => keys i ∈ xs | $ᵗ (I → K)] =
          Pr[fun k => k ∈ xs | $ᵗ K] := by
        have h := uniform_eval (K := K) i
        have he : Pr[fun k => k ∈ xs | (fun keys : I → K => keys i) <$> ($ᵗ (I → K))] =
            Pr[fun k => k ∈ xs | $ᵗ K] := by
          simp only [probEvent_def]
          rw [h]
        simpa only [probEvent_map, Function.comp_def] using he
      rw [he]
      exact uniform_key_mem_list xs
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc]

attribute [local instance 200000] chargedDecidable

theorem independent_keymap_trace_hit {P : PrimSpec} {I : Type} [Fintype I]
    [Fintype P.SpendKey] [Nonempty P.SpendKey] [SampleableType P.SpendKey]
    [SampleableType (I → P.SpendKey)] {α : Type}
    (so : QueryImpl (attackSpec P) ProbComp) (oa : OracleComp (attackSpec P) α)
    (q : Nat) (hq : oa.IsQueryBoundP (charged P) q) :
    Pr[fun z : (α × List P.SpendKey) × (I → P.SpendKey) => ∃ i, z.2 i ∈ z.1.2 | do
      let z ← trace so oa
      let keys ← $ᵗ (I → P.SpendKey)
      pure (z, keys)] ≤ (Fintype.card I : ℝ≥0∞) * q / Fintype.card P.SpendKey := by
  apply probEvent_bind_le_of_forall_le
  intro z hz
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  exact (keymap_hit_list z.2).trans (by gcongr; exact trace_length_bound so oa q hq z hz)

theorem keymap_pair_collision {I K : Type} [Finite I] [Fintype K] [Nonempty K]
    [SampleableType K] [SampleableType (I → K)] (i j : I) (hij : i ≠ j) :
    Pr[fun keys : I → K => keys i = keys j | $ᵗ (I → K)] =
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  classical
  have hd : 𝒮[do
      let keys ← $ᵗ (I → K)
      let u ← $ᵗ K
      pure (Function.update keys i u)] = 𝒮[$ᵗ (I → K)] := by
    rw [evalSPMF_bind_comm]
    exact evalSPMF_uniformSample_bind_update i
  have he : Pr[fun keys : I → K => keys i = keys j | do
      let keys ← $ᵗ (I → K); let u ← $ᵗ K; pure (Function.update keys i u)] =
      Pr[fun keys : I → K => keys i = keys j | $ᵗ (I → K)] := by
    simp only [probEvent_def]
    rw [hd]
  rw [← he]
  rw [probEvent_bind_of_const _ (r := (Fintype.card K : ℝ≥0∞)⁻¹)]
  · simp
  · intro keys _
    simp only [bind_pure_comp, probEvent_map, Function.comp_def,
      Function.update_self, Function.update_of_ne hij.symm]
    simp

theorem keymap_collision_bound {I K : Type} [Fintype I] [Fintype K] [Nonempty K]
    [SampleableType K] [SampleableType (I → K)] :
    Pr[fun keys : I → K => ¬Function.Injective keys | $ᵗ (I → K)] ≤
      ((Fintype.card I * (Fintype.card I - 1) : Nat) : ℝ≥0∞) / Fintype.card K := by
  classical
  let pairs := (Finset.univ : Finset I).offDiag
  have he (keys : I → K) : (¬Function.Injective keys) ↔
      ∃ ij ∈ pairs, keys ij.1 = keys ij.2 := by
    simp only [Function.Injective, not_forall, exists_prop, pairs, Finset.mem_offDiag,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, j, heq, hne⟩
      exact ⟨(i,j), hne, heq⟩
    · rintro ⟨⟨i,j⟩, hne, heq⟩
      exact ⟨i,j,heq,hne⟩
  simp_rw [he]
  refine (probEvent_exists_finset_le_sum pairs ($ᵗ (I → K))
    (fun ij keys => keys ij.1 = keys ij.2)).trans ?_
  apply le_of_eq
  calc
    _ = ∑ _ij ∈ pairs, (Fintype.card K : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact keymap_pair_collision ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : pairs.card = Fintype.card I * (Fintype.card I - 1) := by
        simp [pairs, Finset.offDiag_card, Nat.mul_sub_left_distrib]
      rw [hc, div_eq_mul_inv]

end LeanShieldedPool.WithdrawGame.ROM
