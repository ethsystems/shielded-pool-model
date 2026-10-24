import RecipientGame.CommitOnly.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.RecipientGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model ROMCommit
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

abbrev Joint (adv : ROMCommit.Adversary P cap n) :=
  (hp : P.SpendKey → P.PubKey) × (hn : P.SpendKey × P.Commitment → P.Nullifier) ×
    (hc : Model.Table P cap) × (Bool × ROMCommit.Draw adv hp hn hc)

noncomputable def jointDraws (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : ProbComp (Joint adv) := do
  let hp := P.derivePub
  let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
  let hc ← $ᵗ (Model.Table P cap)
  let d ← atJointDraws sup setup adv hp hn hc
  pure ⟨hp,hn,hc,d⟩

/-- Exact probability that the old validity class fails for a chosen pair and sampled tables. -/
noncomputable def validityFailureProbability (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) : ℝ :=
  (Pr[= true | do let d ← jointDraws sup setup adv; pure d.2.2.2.1]).toReal

noncomputable def collisionProbability (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n) : ℝ :=
  (Pr[= true | do
    let hp := P.derivePub
    let hn : P.SpendKey × P.Commitment → P.Nullifier := fun x => P.nullify x.2 x.1
    let hc ← $ᵗ (Model.Table P cap)
    let d ← atDraws setup adv hp hn hc
    pure (collisionDraw setup adv hp hn hc d)]).toReal

theorem rejection_le_validity_add_collision (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) :
    rejectionProbability sup setup adv ≤ validityFailureProbability sup setup adv + collisionProbability setup adv := by
  classical
  let bad := fun d : Joint adv => d.2.2.2.1 = true
  let col := fun d : Joint adv => collisionDraw setup adv d.1 d.2.1 d.2.2.1 d.2.2.2.2 = true
  let rej := fun d : Joint adv => ROMCommit.rejected sup adv d.1 d.2.1 d.2.2.1 d.2.2.2.2 = true
  have hm : Pr[rej | jointDraws sup setup adv] ≤ Pr[bad | jointDraws sup setup adv] + Pr[col | jointDraws sup setup adv] := by
    apply (probEvent_mono (q := fun d => bad d ∨ col d) ?_).trans (probEvent_or_le _ _ _)
    intro d hd
    simp only [jointDraws, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hd
    obtain ⟨hc,_,x,hx,rfl⟩ := hd
    exact joint_rejection_collision sup setup adv P.derivePub (fun x => P.nullify x.2 x.1) hc x hx
  have hr := ENNReal.toReal_mono (by finiteness) hm
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  have he (f : (d : Joint adv) → Bool) : Pr[fun d => f d = true | jointDraws sup setup adv] =
      Pr[= true | do let d ← jointDraws sup setup adv; pure (f d)] := by
    rw [← probEvent_eq_eq_probOutput]
    exact (probEvent_bind_pure_comp (jointDraws sup setup adv) f (fun b => b = true)).symm
  unfold rejectionProbability validityFailureProbability collisionProbability
  simp only [rej, bad, col] at hr
  rw [he, he, he] at hr
  have hjr (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
      (hc : Model.Table P cap) := joint_forget sup setup adv hp hn hc
        (fun d => pure (ROMCommit.rejected sup adv hp hn hc d))
  have hjc (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
      (hc : Model.Table P cap) := joint_forget sup setup adv hp hn hc
        (fun d => pure (collisionDraw setup adv hp hn hc d))
  simpa only [rej, bad, col, jointDraws, bind_assoc, pure_bind, hjr, hjc] using hr

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Fintype P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem collisionProbability_le (setup : List (Tx P)) (adv : ROMCommit.Adversary P cap n)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    collisionProbability setup adv ≤
      (2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment :=
  atCollision_le setup adv P.derivePub (fun x => P.nullify x.2 x.1) qc qg hq

theorem advantage_le_rom_collisions (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : ROMCommit.Adversary P cap n) (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment +
        validityFailureProbability sup setup adv) / 2 := by
  have h := advantage_le_queryBound sup setup adv qc qg hq
  have hr := rejection_le_validity_add_collision sup setup adv
  have hc := collisionProbability_le setup adv qc qg hq
  linarith

end LeanShieldedPool.RecipientGame.CommitOnly
