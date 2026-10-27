import CommitROM.TableCollision

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model ROMCommit
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

def ValidOn (xs : List (Message P cap × P.Salt)) (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n) : Prop :=
  ∀ hc, (xs.map hc).Nodup → ∀ x,
    x ∈ support (run (WithdrawGame.ROM.answers P.derivePub (fun x => P.nullify x.2 x.1)) hc adv.choose) →
    Valid sup setup P.derivePub (fun x => P.nullify x.2 x.1) hc x.1 x.2.1

theorem validityFailure_le_table_collision (xs : List (Message P cap × P.Salt))
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n)
    (hv : ValidOn xs sup setup adv) :
    validityFailureProbability sup setup adv ≤
      (Pr[fun hc : Model.Table P cap => ¬(xs.map hc).Nodup | $ᵗ (Model.Table P cap)]).toReal := by
  classical
  unfold validityFailureProbability
  simp only [jointDraws, bind_assoc, pure_bind]
  apply ENNReal.toReal_mono (by finiteness)
  rw [← probEvent_eq_eq_probOutput]
  apply (probEvent_bind_le_probEvent_add (p := fun hc => ¬(xs.map hc).Nodup) (ε := 0) ?_).trans_eq (add_zero _)
  intro hc _ hg
  have good : (xs.map hc).Nodup := not_not.mp hg
  apply le_of_eq
  rw [probEvent_eq_eq_probOutput]
  apply probOutput_eq_zero_of_not_mem_support
  simp only [atJointDraws, bind_assoc, pure_bind, support_bind, Set.mem_iUnion]
  rintro ⟨x,hx,h⟩
  have hh := hv hc good x hx
  by_cases hl : RecipientPair (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.1.val)
    (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.2.1.val)
  all_goals simp [hl,hh] at h

theorem validOn_of_old_wellFormed (xs : List (Message P cap × P.Salt))
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n) (m : Nat)
    (W : ∀ hc, (xs.map hc).Nodup → Rejection.WellFormedAdversary
      (P := commitPrim P cap hc) sup
      (setup.map (ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) (legacyAt adv hc) m) :
    ValidOn xs sup setup adv := by
  intro hc hg x hx
  refine ⟨(W hc hg).initial,(W hc hg).setup_run,?_⟩
  apply (W hc hg).worlds
    (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.1.val,
      worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.2.1.val,x.2.2)
  simp only [legacyAt,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff]
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,rfl⟩⟩

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Fintype P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem validityFailure_le_birthday (xs : List (Message P cap × P.Salt)) (hx : xs.Nodup)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n)
    (hv : ValidOn xs sup setup adv) :
    validityFailureProbability sup setup adv ≤
      (xs.length : ℝ)*(xs.length-1)/(2*Fintype.card P.Commitment) :=
  (validityFailure_le_table_collision xs sup setup adv hv).trans (table_collision_le_real xs hx)

theorem advantage_le_birthday (xs : List (Message P cap × P.Salt)) (hx : xs.Nodup)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n)
    (qc qg : Nat) (hq : QueryBound adv qc qg) (hv : ValidOn xs sup setup adv) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment +
        (xs.length : ℝ)*(xs.length-1)/(2*Fintype.card P.Commitment))/2 := by
  have ha := advantage_le_rom_collisions sup setup adv qc qg hq
  have hv' := validityFailure_le_birthday xs hx sup setup adv hv
  linarith


theorem advantage_le_birthday_of_old_wellFormed (xs : List (Message P cap × P.Salt))
    (hx : xs.Nodup) (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (qc qg m : Nat) (hq : QueryBound adv qc qg)
    (W : ∀ hc, (xs.map hc).Nodup → Rejection.WellFormedAdversary
      (P := commitPrim P cap hc) sup
      (setup.map (ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) (legacyAt adv hc) m) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment +
        (xs.length : ℝ)*(xs.length-1)/(2*Fintype.card P.Commitment))/2 :=
  advantage_le_birthday xs hx sup setup adv qc qg hq
    (validOn_of_old_wellFormed xs sup setup adv m W)

end LeanShieldedPool.RecipientGame.CommitOnly
