import RecipientGame.CommitOnly.Funded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly.Funded
open GameCorrespondence CommitROM CommitROM.Model ROMCommit

abbrev Draw (k : Nat) := (hc : H k) × ROMCommit.Draw (adversary k) (hp k) (hn k) hc

noncomputable def draws (k : Nat) : ProbComp (Draw k) := do
  let hc ← $ᵗ H k
  let d ← atDraws (setup k) (adversary k) (hp k) (hn k) hc
  pure ⟨hc,d⟩

def Nonfunded {k : Nat} (x : Draw k) : Prop :=
  match x.2 with
  | none => True
  | some (_,_,txs) => txs.length ≠ 2

noncomputable def Rejected {k : Nat} (x : Draw k) : Prop :=
  ROMCommit.rejected (fun _ => True) (adversary k) (hp k) (hn k) x.1 x.2 = true

noncomputable def fundedPassProbability (k : Nat) : ℝ :=
  (Pr[fun x => ¬(Nonfunded x ∨ Rejected x) | draws k]).toReal

theorem nonfunded_le (k : Nat) : Pr[Nonfunded | draws k] ≤ (k+8 : ℝ≥0∞)⁻¹ := by
  rw [← fallback_probability k]
  unfold draws
  apply probEvent_bind_le_probEvent
  intro hc _ hh
  apply probEvent_eq_zero_iff.mpr
  intro x hx
  simp only [support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hx
  obtain ⟨d,hd,rfl⟩ := hx
  simp only [atDraws] at hd
  rw [run_choose] at hd
  simp only [hh,if_false,pure_bind,legal,if_true,
    support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hd
  obtain ⟨b,_,sampled,hs,rfl⟩ := hd
  cases b <;> simp [worldBack,world,sampleWorld] at hs
  all_goals
    obtain ⟨s,t,rfl⟩ := hs
    simp [Nonfunded,setup]

theorem rejected_probability (k : Nat) :
    (Pr[Rejected | draws k]).toReal = rejectionProbability (fun _ => True) (setup k) (adversary k) := by
  unfold rejectionProbability
  have he := probEvent_bind_pure_comp (draws k)
    (fun x => ROMCommit.rejected (fun _ => True) (adversary k) (hp k) (hn k) x.1 x.2)
    (fun b => b = true)
  simp only [Function.comp_def,probEvent_eq_eq_probOutput] at he
  change (Pr[fun x => ROMCommit.rejected (fun _ => True) (adversary k) (hp k) (hn k) x.1 x.2 = true | draws k]).toReal = _
  rw [← he]
  simp only [draws,bind_assoc,pure_bind]

theorem funded_pass_lower_bound (k : Nat) :
    1 - 33/(k+8 : ℝ) ≤ fundedPassProbability k := by
  have hu := probEvent_or_le (draws k) Nonfunded Rejected
  have hur := ENNReal.toReal_mono (by finiteness) hu
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),rejected_probability] at hur
  have hn := ENNReal.toReal_mono (by finiteness) (nonfunded_le k)
  rw [ENNReal.toReal_inv,ENNReal.toReal_add (by finiteness) (by finiteness)] at hn
  norm_num only [ENNReal.toReal_natCast,ENNReal.toReal_ofNat] at hn
  have hr := rejection_bound k
  have he := congrArg ENNReal.toReal (probEvent_compl (draws k) (fun x => Nonfunded x ∨ Rejected x))
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at he
  simp only [probFailure_eq_zero,tsub_zero,ENNReal.toReal_one] at he
  unfold fundedPassProbability
  have hd : (k+8 : ℝ) ≠ 0 := by positivity
  have hsum : (k+8 : ℝ)⁻¹ + 32/(k+8 : ℝ) = 33/(k+8 : ℝ) := by ring
  linarith

theorem funded_pass_large : 999/1000 < fundedPassProbability 65528 := by
  have h := funded_pass_lower_bound 65528
  norm_num at h
  linarith

noncomputable def old_wellFormed (k : Nat) (hc : H k) :
    Rejection.WellFormedAdversary (P := commitPrim (Prim k) 3 hc) (fun _ => True)
      ((setup k).map (ROMCommit.rebaseTx (hp k) (hn k) hc)) (legacyAt (adversary k) hc) 1 where
  initial := initial k hc
  setup_run := setup_run k hc
  leaf_bound := by simp [initial,DepositData.post,St.empty]
  worlds := by
    intro a ha
    simp only [legacyAt] at ha
    rw [run_choose] at ha
    by_cases hh : fundedCm k hc = ballastCm k hc
    · simp only [hh,if_true,pure_bind,support_pure,Set.mem_singleton_iff] at ha
      subst a
      exact ⟨True.intro,True.intro⟩
    · simp only [hh,if_false,pure_bind,support_pure,Set.mem_singleton_iff] at ha
      subst a
      exact ⟨⟨deterministic_guard k hc false hh,fun _ _ => trivial⟩,
        ⟨deterministic_guard k hc true hh,fun _ _ => trivial⟩⟩

theorem validity_zero_from_old (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) = 0 :=
  validityFailure_eq_zero_of_old_wellFormed _ _ _ 1 (old_wellFormed k)

theorem original_setup_constant_table_rejected (k : Nat) :
    runChecked (St.empty (commitPrim (Prim k) 3 (fun _ => 0)) (fun _ => True))
      ((Rejection.Funded.setup k).map (ROMCommit.rebaseTx (hp k) (hn k) (fun _ => 0))) = none := by
  norm_num [Rejection.Funded.setup,Rejection.Funded.deposit,Rejection.Funded.note,
    ROMCommit.rebaseTx,ROMCommit.rebaseNote,runChecked,stepChecked,DepositData.guard,
    DepositData.post,St.empty,St.leaves,Note.cm,oraclePrim,U128,maxU128]

theorem original_wellFormed_does_not_ensure_oracle_setup (k : Nat) :
    Nonempty (Rejection.WellFormedAdversary (fun _ => True) (Rejection.Funded.setup k)
      (Rejection.Funded.adversary k (pure false)) 2) ∧
    ¬∃ st, Run (P := commitPrim (Prim k) 3 (fun _ => 0)) (fun _ => True)
      ((Rejection.Funded.setup k).map (ROMCommit.rebaseTx (hp k) (hn k) (fun _ => 0))) st := by
  refine ⟨⟨Rejection.Funded.wellFormed k (pure false)⟩,?_⟩
  rintro ⟨st,h⟩
  have hh := runChecked_complete h
  rw [original_setup_constant_table_rejected] at hh
  contradiction

end LeanShieldedPool.RecipientGame.CommitOnly.Funded
