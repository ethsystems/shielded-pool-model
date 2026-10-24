import RecipientGame.ROMCommit.Rejection
import CommitROM.Lower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.RecipientGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model ROMCommit
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

noncomputable def experiment (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : ProbComp Bool := do
  let hp := P.derivePub
  let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
  let hc ← $ᵗ (Model.Table P cap)
  atExperiment sup setup adv hp hn hc

noncomputable def unguarded (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n) : ProbComp Bool := do
  let hp := P.derivePub
  let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
  let hc ← $ᵗ (Model.Table P cap)
  atUnguarded setup adv hp hn hc

noncomputable def rejectionProbability (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : ℝ := (Pr[= true | do
  let hp := P.derivePub
  let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
  let hc ← $ᵗ (Model.Table P cap)
  let d ← atDraws setup adv hp hn hc
  pure (ROMCommit.rejected sup adv hp hn hc d)]).toReal

noncomputable def advantage (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : ℝ := |(Pr[= true | experiment sup setup adv]).toReal - 1/2|

theorem rejection_transport (sup : P.Token → Prop) (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n) :
    (experiment sup setup adv).boolDistAdvantage (unguarded setup adv) ≤
      rejectionProbability sup setup adv / 2 := by
  classical
  let draws := do
    let hp := P.derivePub
    let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
    let hc ← $ᵗ (Model.Table P cap)
    let d ← atDraws setup adv hp hn hc
    pure (⟨hp,hn,hc,d⟩ : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) × ROMCommit.Draw adv hp hn hc)
  let bad := fun d : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) ×
      ROMCommit.Draw adv hp hn hc => ROMCommit.rejected sup adv d.1 d.2.1 d.2.2.1 d.2.2.2
  let resp := fun d : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) ×
      ROMCommit.Draw adv hp hn hc => ROMCommit.response adv d.1 d.2.1 d.2.2.1 d.2.2.2
  have h := RecipientGame.rejection_distance_le draws bad resp
  unfold experiment atExperiment unguarded atUnguarded ROMCommit.checkedResponse rejectionProbability
  simpa only [draws, bad, resp, bind_assoc, pure_bind] using h

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem unguarded_bias_le (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    |(Pr[= true | unguarded setup adv]).toReal - 1/2| ≤
      (2*n : ℝ) * (qc+qg+4*setup.length+6*n) / Fintype.card P.Salt :=
  atUnguarded_bias_le setup adv P.derivePub (fun x => P.nullify x.2 x.1) qc qg hq

theorem advantage_le_queryBound (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage sup setup adv ≤
      (2*n : ℝ) * (qc+qg+4*setup.length+6*n) / Fintype.card P.Salt +
        rejectionProbability sup setup adv / 2 := by
  have hu := unguarded_bias_le setup adv qc qg hq
  have hr := rejection_transport sup setup adv
  have ht := abs_sub_le (Pr[= true | experiment sup setup adv]).toReal
    (Pr[= true | unguarded setup adv]).toReal (1/2)
  unfold advantage ProbComp.boolDistAdvantage at *
  linarith

end LeanShieldedPool.RecipientGame.CommitOnly
