import CommitROM.Pair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}

structure BatchAdversary (M S C : Type) {I : Type} (aux : OracleSpec I) (n : Nat) where
  State : Type
  choose : OracleComp (attackSpec M S C aux) ({ms : List M // ms.length ≤ n} × State)
  guess : State → List C → OracleComp (attackSpec M S C aux) Bool

def BatchQueryBound {n : Nat} (adv : BatchAdversary M S C aux n) (qc qg : Nat) : Prop :=
  adv.choose.IsQueryBoundP (charged (C := C) (aux := aux)) qc ∧
    ∀ s cs, (adv.guess s cs).IsQueryBoundP (charged (C := C) (aux := aux)) qg

def commitList [SampleableType S] : List M → OracleComp (attackSpec M S C aux) (List C)
  | [] => pure []
  | m :: ms => do
    let s ← liftComp ($ᵗ S) (attackSpec M S C aux)
    let c ← liftM ((attackSpec M S C aux).query (.inr (.inl (m,s))))
    let cs ← commitList ms
    pure (c :: cs)

def uniformList [SampleableType C] : Nat → ProbComp (List C)
  | 0 => pure []
  | n+1 => do let c ← $ᵗ C; let cs ← uniformList n; pure (c :: cs)

theorem commitList_bound [SampleableType S] (ms : List M) :
    (commitList (S := S) (C := C) (aux := aux) ms).IsQueryBoundP
      (charged (C := C) (aux := aux)) ms.length := by
  induction ms with
  | nil => simp [commitList]
  | cons m ms ih =>
    unfold commitList
    apply (isQueryBoundP_bind (n := 0) (m := ms.length+1) (coins_bound _ 0) ?_).mono (by simp)
    intro s _
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr (by omega), fun c => by simpa [charged] using ih⟩

noncomputable def batchTest [SampleableType S] {n : Nat}
    (adv : BatchAdversary M S C aux (n+1)) (f : M → C) :
    OracleComp (attackSpec M S C aux) Bool := do
  let x ← adv.choose
  match x.1.val with
  | [] => adv.guess x.2 []
  | m :: ms => do
    let cs ← commitList ms
    adv.guess x.2 (f m :: cs)

theorem batchTest_bound [SampleableType S] {n : Nat}
    (adv : BatchAdversary M S C aux (n+1)) (qc qg : Nat)
    (hq : BatchQueryBound adv qc qg) (f : M → C) :
    (batchTest adv f).IsQueryBoundP (charged (C := C) (aux := aux)) (qc+(n+qg)) := by
  unfold batchTest
  apply isQueryBoundP_bind hq.1
  intro x _
  have hl := x.1.property
  split
  · exact (hq.2 _ _).mono (by omega)
  · rename_i m ms he
    have ht : ms.length ≤ n := by rw [he] at hl; simp only [List.length_cons] at hl; omega
    exact (isQueryBoundP_bind (commitList_bound ms) (fun cs _ => hq.2 _ _)).mono (by omega)

noncomputable def tailReduction [SampleableType C] {n : Nat}
    (adv : BatchAdversary M S C aux (n+1)) : BatchAdversary M S C aux n where
  State := adv.State × Option C
  choose := do
    let x ← adv.choose
    match he : x.1.val with
    | [] => pure (⟨[],by simp⟩,(x.2,none))
    | _ :: ms => do
      let c ← liftComp ($ᵗ C) (attackSpec M S C aux)
      pure (⟨ms,by have hl := x.1.property; rw [he] at hl; simp only [List.length_cons] at hl; omega⟩,(x.2,some c))
  guess := fun s cs => adv.guess s.1 (s.2.toList ++ cs)

theorem tailReduction_bound [SampleableType C] {n : Nat}
    (adv : BatchAdversary M S C aux (n+1)) (qc qg : Nat)
    (hq : BatchQueryBound adv qc qg) : BatchQueryBound (tailReduction adv) qc qg := by
  constructor
  · apply (isQueryBoundP_bind (n := qc) (m := 0) hq.1 ?_).mono (by simp)
    intro x _
    change (match he : x.1.val with
      | [] => pure ((⟨[], by simp⟩ : {ms : List M // ms.length ≤ n}), (x.2, (none : Option C)))
      | _ :: ms => do
        let c ← liftComp ($ᵗ C) (attackSpec M S C aux)
        pure ((⟨ms, by have hl := x.1.property; rw [he] at hl; simp only [List.length_cons] at hl; omega⟩ : {ms : List M // ms.length ≤ n}), (x.2, some c))).IsQueryBoundP _ 0
    split
    · simp
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (coins_bound (M := M) (S := S) (aux := aux) ($ᵗ C) 0)
  · intro s cs; exact hq.2 _ _

variable [Finite M] [Fintype S] [Finite C] [Nonempty C]
  [SampleableType S] [SampleableType C]
  [SampleableType (M × S → C)] [SampleableType (M → C)]

noncomputable def batchReal {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux n) : ProbComp Bool := do
  let h ← $ᵗ (M × S → C)
  let x ← run other h adv.choose
  let cs ← run other h (commitList x.1.val)
  run other h (adv.guess x.2 cs)

noncomputable def batchIdeal {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux n) : ProbComp Bool := do
  let h ← $ᵗ (M × S → C)
  let x ← run other h adv.choose
  let cs ← uniformList x.1.val.length
  run other h (adv.guess x.2 cs)

theorem run_commitList_cons (other : QueryImpl aux Id) (h : M × S → C) (m : M) (ms : List M) :
    run other h (commitList (aux := aux) (m :: ms)) = (do
      let s ← $ᵗ S
      let cs ← run other h (commitList ms)
      pure (h (m,s) :: cs)) := by
  simp only [commitList, run, simulateQ_bind, simulateQ_pure]
  have hs := run_coins other h ($ᵗ S)
  unfold run at hs
  rw [hs]
  apply bind_congr; intro s
  simp only [simulateQ_query]
  change (pure (h (m,s)) : ProbComp C) >>= _ = _
  simp

theorem batch_real_eq {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux (n+1)) :
    𝒮[real other (batchTest adv)] = 𝒮[batchReal other adv] := by
  unfold real batchReal
  rw [evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left; intro h
  simp only [batchTest, run, simulateQ_bind]
  rw [evalSPMF_bind_comm ($ᵗ S)]
  apply evalSPMF_bind_congr_left; intro x
  cases he : x.1.val with
  | nil =>
    simp only [commitList, simulateQ_pure, pure_bind]
    exact evalSPMF_bind_const_neverFails _ (by simp) _
  | cons m ms =>
    have hr := run_commitList_cons (aux := aux) other h m ms
    unfold run at hr
    simp only [he, hr, bind_assoc, pure_bind, saltCoord, Function.comp_def]
    simp only [simulateQ_bind]

theorem batch_ideal_eq_tail {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux (n+1)) :
    𝒮[ideal other (batchTest adv)] = 𝒮[batchReal other (tailReduction adv)] := by
  unfold ideal batchReal
  apply evalSPMF_bind_congr_left; intro h
  simp only [batchTest, tailReduction, run, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  rw [evalSPMF_bind_comm ($ᵗ (M → C))]
  apply evalSPMF_bind_congr_left; intro x
  rcases x with ⟨⟨ms, hl⟩, st⟩
  cases ms with
  | nil =>
    simp only [commitList, simulateQ_pure, pure_bind, Option.toList_none, List.nil_append]
    exact evalSPMF_bind_const_neverFails _ (by simp) _
  | cons m ms =>
    simp only [simulateQ_bind, simulateQ_pure]
    have hc := run_coins other h ($ᵗ C)
    unfold run at hc
    rw [hc]
    simp only [bind_assoc, pure_bind, Option.toList_some, List.singleton_append]
    rw [evalSPMF_bind_comm ($ᵗ (M → C))]
    rw [evalSPMF_bind_comm ($ᵗ C)]
    apply evalSPMF_bind_congr_left; intro cs
    exact uniform_eval_bind m (fun c => simulateQ _ (adv.guess st (c :: cs)))

theorem batchIdeal_tail_eq {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux (n+1)) :
    batchIdeal other (tailReduction adv) = batchIdeal other adv := by
  simp only [batchIdeal, tailReduction, run, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  apply bind_congr; intro h
  apply bind_congr; intro x
  rcases x with ⟨⟨ms, hl⟩, st⟩
  cases ms with
  | nil => simp [uniformList, simulateQ_pure]
  | cons m ms =>
    simp only [List.length_cons, uniformList, simulateQ_bind, simulateQ_pure]
    have hc := run_coins other h ($ᵗ C)
    unfold run at hc
    rw [hc]
    simp [bind_assoc]

/-- A variable-length batch shares one oracle. Every later challenge costs one query. -/
theorem batch_distance_le {n : Nat} (other : QueryImpl aux Id)
    (adv : BatchAdversary M S C aux n) (qc qg : Nat) (hq : BatchQueryBound adv qc qg) :
    (batchReal other adv).boolDistAdvantage (batchIdeal other adv) ≤
      (n : ℝ) * (qc + qg + n) / Fintype.card S := by
  induction n with
  | zero =>
    have he : batchReal other adv = batchIdeal other adv := by
      unfold batchReal batchIdeal
      apply bind_congr; intro h
      apply bind_congr; intro x
      have hx : x.1.val = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero x.1.property)
      simp [hx, commitList, uniformList, run, simulateQ_pure]
    simp [he, ProbComp.boolDistAdvantage]
  | succ n ih =>
    have hs := switch_bound other (batchTest adv) (qc+(n+qg)) (batchTest_bound adv qc qg hq)
    unfold ProbComp.boolDistAdvantage at hs
    rw [probOutput_congr (x := true) rfl (batch_real_eq other adv),
      probOutput_congr (x := true) rfl (batch_ideal_eq_tail other adv)] at hs
    have ht := ih (tailReduction adv) (tailReduction_bound adv qc qg hq)
    rw [batchIdeal_tail_eq] at ht
    have tri := ProbComp.boolDistAdvantage_triangle (batchReal other adv)
      (batchReal other (tailReduction adv)) (batchIdeal other adv)
    change (batchReal other adv).boolDistAdvantage (batchReal other (tailReduction adv)) ≤ _ at hs
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hc : (0:ℝ) ≤ qc := Nat.cast_nonneg qc
    have hg : (0:ℝ) ≤ qg := Nat.cast_nonneg qg
    have hd : (0:ℝ) ≤ (Fintype.card S : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    push_cast at hs ⊢
    simp only [div_eq_mul_inv] at hs ht ⊢
    nlinarith [mul_nonneg hn hd, mul_nonneg hc hd, mul_nonneg hg hd]

end LeanShieldedPool.CommitROM
