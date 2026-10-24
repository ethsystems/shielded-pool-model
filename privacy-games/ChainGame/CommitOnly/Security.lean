import ChainGame.CommitOnly.Hiding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.ChainGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model
open RecipientGame.ROMCommit (projected projected_length messages messages_length)
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Model.Table P cap)] [SampleableType (Message P cap → P.Commitment)]

theorem reduction_ideal_fair (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    Pr[= true | batchIdeal (WithdrawGame.ROM.answers hp hn) (reduction setup adv hn)] = 1/2 := by
  classical
  unfold batchIdeal
  rw [probOutput_bind_of_const ($ᵗ (Model.Table P cap)) (r := 1/2)]
  · simp
  · intro hc _
    rw [run_reduction_choose]
    simp only [bind_assoc]
    rw [probOutput_bind_of_const (run (WithdrawGame.ROM.answers hp hn) hc adv.choose) (r := 1/2)]
    · simp
    · intro x _
      by_cases hl : Aligned x.1.val x.2.1.val ∧ PoolGame.LegalChallenge (projected hp hn hc (bodies x.1.val)) (projected hp hn hc (bodies x.2.1.val))
      · simp only [hl, true_and, if_true, bind_assoc, pure_bind]
        have hlen : x.1.val.length = x.2.1.val.length := by
          simpa only [projected_length, bodies_length] using PoolGame.lengths_match_of_legalChallenge hl.2
        have hm (b : Bool) : (messages (bodies (if b then x.2.1 else x.1).val)).length = 2*x.1.val.length := by
          cases b <;> simp [messages_length, bodies_length, hlen]
        simp only [hm, reduction, run, simulateQ_bind, simulateQ_pure]
        rw [probOutput_bind_bind_swap ($ᵗ Bool)]
        rw [probOutput_bind_of_const (uniformList (C := P.Commitment) (2*x.1.val.length)) (r := 1/2)]
        · simp
        · intro cs _
          exact RecipientGame.Rejection.Funded.fair_guess _
      · simp only [hl, true_and, if_false, pure_bind, List.length_nil, uniformList, reduction]
        rw [run_coins]
        simp

/-- An arbitrary fixed-reference recipient chain, with no statistical hiding hypothesis. -/
theorem atUnguarded_bias_le (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    |(Pr[= true | do let hc ← $ᵗ (Model.Table P cap); atUnguarded setup adv hp hn hc]).toReal - 1/2| ≤
      (2*n : ℝ) * (qc+qg+4*setup.length+6*n) / Fintype.card P.Salt := by
  have hb := batch_distance_le (WithdrawGame.ROM.answers hp hn) (reduction setup adv hn)
    (qc+4*setup.length+4*n) qg (reduction_bound setup adv hn qc qg hq)
  unfold ProbComp.boolDistAdvantage at hb
  rw [reduction_real_eq, reduction_ideal_fair] at hb
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hb
  convert hb using 1
  push_cast
  ring

theorem unguarded_bias_le (setup : List (Tx P)) (adv : Adversary P cap n)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    |(Pr[= true | unguarded setup adv]).toReal - 1/2| ≤
      (2*n : ℝ) * (qc+qg+4*setup.length+6*n) / Fintype.card P.Salt :=
  atUnguarded_bias_le setup adv P.derivePub (fun x => P.nullify x.2 x.1) qc qg hq

/-- Query-bounded ChainGame recipient privacy in the commitment-only oracle model. -/
theorem advantage_le_queryBound (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage sup setup adv ≤
      (2*n : ℝ) * (qc+qg+4*setup.length+6*n) / Fintype.card P.Salt +
        rejectionProbability sup setup adv / 2 := by
  have hu := unguarded_bias_le setup adv qc qg hq
  have hr := rejection_transport sup setup adv
  have ht := abs_sub_le (Pr[= true | experiment sup setup adv]).toReal
    (Pr[= true | unguarded setup adv]).toReal (1/2)
  unfold advantage ProbComp.boolDistAdvantage at *
  linarith

end LeanShieldedPool.ChainGame.CommitOnly
