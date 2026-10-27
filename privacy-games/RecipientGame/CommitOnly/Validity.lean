import RecipientGame.CommitOnly.Rejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model ROMCommit
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

/-- Validity on the support of the choice computation, for each commitment table. -/
def SupportedValidity (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : Prop :=
  ∀ hc x, x ∈ support (run (WithdrawGame.ROM.answers P.derivePub (fun x => P.nullify x.2 x.1)) hc adv.choose) →
    Valid sup setup P.derivePub (fun x => P.nullify x.2 x.1) hc x.1 x.2.1

theorem validityFailure_eq_zero (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (hv : SupportedValidity sup setup adv) :
    validityFailureProbability sup setup adv = 0 := by
  classical
  unfold validityFailureProbability
  suffices hz : Pr[= true | do let d ← jointDraws sup setup adv; pure d.2.2.2.1] = 0 by
    rw [hz, ENNReal.toReal_zero]
  apply probOutput_eq_zero_of_not_mem_support
  simp only [jointDraws, atJointDraws, bind_assoc, pure_bind, support_bind, Set.mem_iUnion]
  rintro ⟨hc, _, x, hx, h⟩
  have hh := hv hc x hx
  by_cases hl : RecipientPair (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.1.val)
    (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.2.1.val)
  all_goals simp [hl,hh] at h

/-- The old RecipientGame adversary at one table, retaining its complete choice distribution. -/
def legacyAt (adv : ROMCommit.Adversary P cap n) (hc : Model.Table P cap) :
    RecipientGame.Adversary (commitPrim P cap hc) where
  State := adv.State
  chooseWorlds := do
    let (l,r,s) ← run (WithdrawGame.ROM.answers P.derivePub (fun x => P.nullify x.2 x.1)) hc adv.choose
    pure (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc l.val,
      worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc r.val,s)
  distinguish := fun _ => pure false

theorem supportedValidity_of_old_wellFormed (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (m : Nat)
    (W : ∀ hc, Rejection.WellFormedAdversary (P := commitPrim P cap hc) sup
      (setup.map (ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) (legacyAt adv hc) m) :
    SupportedValidity sup setup adv := by
  intro hc x hx
  refine ⟨(W hc).initial, (W hc).setup_run, ?_⟩
  apply (W hc).worlds
    (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.1.val,
      worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.2.1.val, x.2.2)
  simp only [legacyAt, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,rfl⟩⟩

theorem validityFailure_eq_zero_of_old_wellFormed (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (m : Nat)
    (W : ∀ hc, Rejection.WellFormedAdversary (P := commitPrim P cap hc) sup
      (setup.map (ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) (legacyAt adv hc) m) :
    validityFailureProbability sup setup adv = 0 :=
  validityFailure_eq_zero sup setup adv (supportedValidity_of_old_wellFormed sup setup adv m W)

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Fintype P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem advantage_le_of_supportedValidity (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (qc qg : Nat) (hq : QueryBound adv qc qg)
    (hv : SupportedValidity sup setup adv) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment) / 2 := by
  simpa only [validityFailure_eq_zero sup setup adv hv, add_zero] using
    advantage_le_rom_collisions sup setup adv qc qg hq

theorem advantage_le_of_old_wellFormed (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (qc qg m : Nat) (hq : QueryBound adv qc qg)
    (W : ∀ hc, Rejection.WellFormedAdversary (P := commitPrim P cap hc) sup
      (setup.map (ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) (legacyAt adv hc) m) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment) / 2 :=
  advantage_le_of_supportedValidity sup setup adv qc qg hq
    (supportedValidity_of_old_wellFormed sup setup adv m W)

end LeanShieldedPool.RecipientGame.CommitOnly
