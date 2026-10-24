import RecipientGame.CommitOnly.TwoFunded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly.TwoFunded
open GameCorrespondence CommitROM CommitROM.Model ROMCommit

theorem valid_iff (k : Nat) (hc : H k) :
    Valid (fun _ => True) (setup k) (hp k) (hn k) hc (world k false) (world k true) ↔
      hc (coord k 0) ≠ hc (coord k 1) := by
  constructor
  · rintro ⟨st,hrun,_⟩
    have hr := RecipientGame.runChecked_complete hrun
    by_contra he
    have he' : hc (coord k 0) = hc (coord k 1) := he
    have hnone : RecipientGame.runChecked (St.empty (commitPrim (Prim k) 2 hc) (fun _ => True))
        ((setup k).map (rebaseTx (hp k) (hn k) hc)) = none := by
      simp [RecipientGame.runChecked,RecipientGame.stepChecked,setup,Rejection.Funded.setup,
        deposit,Rejection.Funded.deposit,note,Rejection.Funded.note,rebaseTx,ROMCommit.rebaseNote,
        DepositData.guard,DepositData.post,St.empty,St.leaves,Note.cm,oraclePrim,U128,maxU128,
        hp,hn,Prim,Rejection.Funded.Prim,coord] at he' ⊢
      exact he'.symm
    rw [hnone] at hr
    contradiction
  · intro h
    exact ⟨initial k hc,setup_run k hc h,⟨deterministic_guard k hc false h,fun _ _ => trivial⟩,
      ⟨deterministic_guard k hc true h,fun _ _ => trivial⟩⟩

theorem validity_exact (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) = 1/(k+8 : ℝ) := by
  classical
  have he : Pr[= true | do let d ← jointDraws (fun _ => True) (setup k) (adversary k); pure d.2.2.2.1] =
      Pr[fun hc : H k => hc (coord k 0) = hc (coord k 1) | $ᵗ (H k)] := by
    simp only [jointDraws,atJointDraws,adversary,run,simulateQ_pure,pure_bind,bind_assoc]
    have hl := legal k
    have hv := valid_iff k
    dsimp [hp,hn,Prim,Rejection.Funded.Prim] at hl hv
    simp only [hl,if_true,hv,not_not,bind_assoc,pure_bind]
    rw [probOutput_bind_eq_tsum]
    rw [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro hc
    rw [← bind_assoc,probOutput_bind_const,probFailure_eq_zero,tsub_zero,one_mul]
    by_cases he : hc (coord k 0) = hc (coord k 1)
    all_goals simp only [he,decide_true,decide_false,probOutput_bind_const,probFailure_eq_zero,
      tsub_zero,one_mul,probOutput_pure,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false,mul_one,mul_zero]

  unfold validityFailureProbability
  rw [he,WithdrawGame.ROM.keymap_pair_collision (coord k 0) (coord k 1) (by simp [coord,Fin.ext_iff])]
  simp only [Prim,Rejection.Funded.Prim,ENNReal.toReal_inv,Fintype.card_fin,ENNReal.toReal_natCast,Nat.cast_add,Nat.cast_ofNat,one_div]
  norm_num [ENNReal.toReal_add]

theorem dropping_validity_collision_false (k : Nat) :
    ¬ validityFailureProbability (fun _ => True) (setup k) (adversary k) ≤ 0 := by
  rw [validity_exact]
  exact not_le.mpr (by positivity)

theorem run_guess (k : Nat) (hc : H k) (a b c d : (Prim k).Nullifier)
    (o p : (Prim k).Commitment) :
    run (WithdrawGame.ROM.answers (hp k) (hn k)) hc
      ((adversary k).guess () [.deposit a ,.deposit b,.transfer c d o p]) =
      pure (decide (hc (coord k 2) ≠ o)) := by
  simp only [adversary,guess,run,simulateQ_bind]
  have h := run_cmNote (cap := 2) (hp k) (hn k) hc (note k false 2)
  unfold run at h
  rw [h,pure_bind]
  rfl


theorem guess_not_zero_query (k : Nat) : ¬ QueryBound (adversary k) 0 0 := by
  intro h
  have hh := h.2 () []
  change (liftM ((Spec (Prim k) 2).query (.inr (.inl (coord k 2)))) >>=
    fun _ => pure false : OracleComp (Spec (Prim k) 2) Bool).IsQueryBoundP (CommitROM.charged (C := (Prim k).Commitment)
      (aux := WithdrawGame.ROM.hashSpec (Prim k))) 0 at hh
  rw [isQueryBoundP_query_bind_iff] at hh
  simpa [CommitROM.charged] using hh.1

theorem small_bounds :
    validityFailureProbability (fun _ => True) (setup 65528) (adversary 65528) = 1/65536 ∧
    rejectionProbability (fun _ => True) (setup 65528) (adversary 65528) < 1/1000 ∧
    advantage (fun _ => True) (setup 65528) (adversary 65528) < 1/1000 := by
  constructor
  · convert validity_exact 65528 using 1
    norm_num
  constructor
  · exact (rejection_bound 65528).trans_lt (by norm_num)
  · exact (privacy_bound 65528).trans_lt (by norm_num)

end LeanShieldedPool.RecipientGame.CommitOnly.TwoFunded
