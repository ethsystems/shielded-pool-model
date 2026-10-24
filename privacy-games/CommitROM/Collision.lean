import CommitROM.Batch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}

/-- A new output repeats an existing commitment or an earlier output. -/
def Collision : List C → List C → Prop
  | _, [] => False
  | old, c :: cs => c ∈ old ∨ Collision (c :: old) cs

def collisionCost (m : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m + collisionCost (m+1) n

theorem collisionCost_le (m n : Nat) : collisionCost m n ≤ n*(m+n) := by
  induction n generalizing m with
  | zero => simp [collisionCost]
  | succ n ih =>
    simp only [collisionCost]
    have h := ih (m+1)
    nlinarith

theorem uniform_mem_le [Fintype C] [SampleableType C] (old : List C) :
    Pr[fun c => c ∈ old | $ᵗ C] ≤ (old.length : ℝ≥0∞) / Fintype.card C := by
  classical
  induction old with
  | nil => simp
  | cons c old ih =>
    simp only [List.mem_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h := probEvent_or_le ($ᵗ C) (fun x => x = c) (fun x => x ∈ old)
    rw [probEvent_eq_eq_probOutput, probOutput_uniformSample] at h
    refine h.trans ((add_le_add le_rfl ih).trans_eq ?_)
    simp only [div_eq_mul_inv]
    ring

theorem uniformList_collision_le [Fintype C] [SampleableType C] (old : List C) (n : Nat) :
    Pr[fun cs => Collision old cs | uniformList (C := C) n] ≤
      (collisionCost old.length n : ℝ≥0∞) / Fintype.card C := by
  classical
  induction n generalizing old with
  | zero => simp [uniformList, Collision, collisionCost]
  | succ n ih =>
    unfold uniformList
    have h := probEvent_bind_le_probEvent_add
      (mx := ($ᵗ C)) (p := fun c => c ∈ old)
      (ε := (collisionCost (old.length+1) n : ℝ≥0∞) / Fintype.card C)
      (q := fun cs => Collision old cs)
      (my := fun c => do let cs ← uniformList (C := C) n; pure (c :: cs))
      (by
        intro c _ hc
        simpa [probEvent_bind_pure_comp, Function.comp_def, Collision, hc] using ih (c :: old))
    refine h.trans ((add_le_add (uniform_mem_le old) le_rfl).trans_eq ?_)
    simp only [collisionCost, Nat.cast_add, div_eq_mul_inv]
    ring

noncomputable def collisionTest {n : Nat} (adv : BatchAdversary M S C aux n)
    (old : adv.State → List C) : BatchAdversary M S C aux n := by
  classical
  exact {
    State := adv.State
    choose := adv.choose
    guess := fun s cs => pure (decide (Collision (old s) cs)) }

theorem collisionTest_bound {n : Nat} (adv : BatchAdversary M S C aux n)
    (old : adv.State → List C) (qc : Nat)
    (hq : adv.choose.IsQueryBoundP (charged (C := C) (aux := aux)) qc) :
    BatchQueryBound (collisionTest adv old) qc 0 := by
  classical
  exact ⟨hq,fun _ _ => by simp [collisionTest]⟩

variable [Finite M] [Fintype S] [Fintype C] [Nonempty C]
  [SampleableType S] [SampleableType C]
  [SampleableType (M × S → C)] [SampleableType (M → C)]

/-- ROM range collisions, with the oracle-query and salt-reuse correction. -/
theorem batch_collision_le {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux n) (old : adv.State → List C) (m qc : Nat)
    (hm : ∀ s, (old s).length ≤ m)
    (hq : adv.choose.IsQueryBoundP (charged (C := C) (aux := aux)) qc) :
    (Pr[= true | batchReal other (collisionTest adv old)]).toReal ≤
      (n : ℝ)*(qc+n)/Fintype.card S + (n : ℝ)*(m+n)/Fintype.card C := by
  classical
  have hb := batch_distance_le other (collisionTest adv old) qc 0 (collisionTest_bound adv old qc hq)
  have hi : Pr[= true | batchIdeal other (collisionTest adv old)] ≤
      ((n*(m+n) : Nat) : ℝ≥0∞) / Fintype.card C := by
    rw [← probEvent_eq_eq_probOutput]
    unfold batchIdeal
    apply probEvent_bind_le_of_forall_le
    intro h _
    apply probEvent_bind_le_of_forall_le
    intro x _
    have hu := uniformList_collision_le (old x.2) x.1.val.length
    have hc : collisionCost (old x.2).length x.1.val.length ≤ n*(m+n) :=
      (collisionCost_le _ _).trans (Nat.mul_le_mul x.1.property (by have := hm x.2; have := x.1.property; omega))
    have hh : (collisionCost (old x.2).length x.1.val.length : ℝ≥0∞) / Fintype.card C ≤
        ((n*(m+n) : Nat) : ℝ≥0∞) / Fintype.card C := by
      simp only [div_eq_mul_inv]
      exact mul_le_mul' (by exact_mod_cast hc) le_rfl
    change Pr[fun b : Bool => b = true | uniformList (C := C) x.1.val.length >>=
      pure ∘ (fun cs => decide (Collision (old x.2) cs))] ≤ _
    rw [probEvent_bind_pure_comp]
    simpa only [Function.comp_def, decide_eq_true_eq] using hu.trans hh
  have hir := ENNReal.toReal_mono (by finiteness) hi
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hir
  push_cast at hir
  unfold ProbComp.boolDistAdvantage at hb
  simp only [Nat.cast_zero, add_zero] at hb
  linarith [le_abs_self ((Pr[= true | batchReal other (collisionTest adv old)]).toReal -
    (Pr[= true | batchIdeal other (collisionTest adv old)]).toReal)]

end LeanShieldedPool.CommitROM
