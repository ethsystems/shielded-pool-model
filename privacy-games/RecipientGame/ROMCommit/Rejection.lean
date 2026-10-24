import RecipientGame.ROMCommit.Collision

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.ROMCommit
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}

/-- Exactly the old static validity class: accepted common setup, then all-salt deterministic guards. -/
def Valid (sup : P.Token → Prop) (setup : List (Tx P))
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) (l r : World P cap n) : Prop :=
  ∃ st, Run (P := oraclePrim P cap hp hn hc) sup (setup.map (rebaseTx hp hn hc)) st ∧
    Rejection.WellFormed st (worldBack hp hn hc l.val) ∧
    Rejection.WellFormed st (worldBack hp hn hc r.val)

variable [SampleableType P.Salt]

noncomputable def atJointDraws (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    ProbComp (Bool × Draw adv hp hn hc) := by
  classical
  exact do
    let (l,r,s) ← run (WithdrawGame.ROM.answers hp hn) hc adv.choose
    let bad := decide (¬Valid sup setup hp hn hc l r)
    if RecipientGame.RecipientPair (worldBack hp hn hc l.val) (worldBack hp hn hc r.val) then do
      let b ← $ᵗ Bool
      let sampled ← RecipientGame.sampleWorld (if b then worldBack hp hn hc r.val else worldBack hp hn hc l.val)
      pure (bad,some (s,b,setup.map (rebaseTx hp hn hc) ++ sampled.map Tx.transfer))
    else pure (bad,none)

theorem joint_forget {α : Type} (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (f : Draw adv hp hn hc → ProbComp α) :
    (do let d ← atJointDraws sup setup adv hp hn hc; f d.2) = (atDraws setup adv hp hn hc >>= f) := by
  classical
  simp only [atJointDraws, atDraws, bind_assoc]
  apply bind_congr; intro x
  split <;> simp only [bind_assoc, pure_bind]

theorem outputs_back (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (es : List (PoolGame.Event (gamePrim (oraclePrim P cap hp hn hc)))) :
    outputs (es.map (eventBack hp hn hc)) = outputs (P := oraclePrim P cap hp hn hc) es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [eventBack, outputs, ih]

theorem joint_rejection_collision (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (d : Bool × Draw adv hp hn hc) (hd : d ∈ support (atJointDraws sup setup adv hp hn hc)) :
    rejected sup adv hp hn hc d.2 = true → d.1 = true ∨ collisionDraw setup adv hp hn hc d.2 = true := by
  classical
  simp only [atJointDraws, support_bind, Set.mem_iUnion] at hd
  obtain ⟨x,_,hd⟩ := hd
  by_cases hl : RecipientGame.RecipientPair (worldBack hp hn hc x.1.val) (worldBack hp hn hc x.2.1.val)
  · simp only [hl, if_true, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hd
    obtain ⟨b,_,sampled,hs,rfl⟩ := hd
    intro hrej
    by_cases hv : Valid sup setup hp hn hc x.1 x.2.1
    · right
      obtain ⟨st,hrun,hwl,hwr⟩ := hv
      have hw : Rejection.WellFormed st
          (if b then worldBack hp hn hc x.2.1.val else worldBack hp hn hc x.1.val) := by
        cases b <;> assumption
      have hcRun := RecipientGame.runChecked_complete hrun
      have hre : RecipientGame.runChecked st (sampled.map Tx.transfer) = none := by
        simpa only [rejected, RecipientGame.runChecked_append, hcRun, Option.bind_some,
          Option.isNone_iff_eq_none] using hrej
      have hcoll := (Rejection.rejection_iff_collision st _ sampled hw hs).mp hre
      rw [collision_iff_outputs, run_leaves hrun] at hcoll
      simp only [collisionDraw, decide_eq_true_eq]
      have hlen : (setup.map (rebaseTx hp hn hc)).length = setup.length := List.length_map _
      rw [← hlen, List.take_left, List.drop_left, outputs_back, outputs_back]
      exact hcoll
    · left
      simp [hv]
  · simp only [hl, if_false, support_pure, Set.mem_singleton_iff] at hd
    subst d
    simp [rejected]

variable [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)] [SampleableType (Model.Table P cap)]

abbrev Joint (adv : Adversary P cap n) :=
  (hp : P.SpendKey → P.PubKey) × (hn : P.SpendKey × P.Commitment → P.Nullifier) ×
    (hc : Model.Table P cap) × (Bool × Draw adv hp hn hc)

noncomputable def jointDraws (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) : ProbComp (Joint adv) := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
  let hc ← $ᵗ (Model.Table P cap)
  let d ← atJointDraws sup setup adv hp hn hc
  pure ⟨hp,hn,hc,d⟩

/-- Exact probability that the old validity class fails for a chosen pair and sampled tables. -/
noncomputable def validityFailureProbability (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) : ℝ :=
  (Pr[= true | do let d ← jointDraws sup setup adv; pure d.2.2.2.1]).toReal

noncomputable def collisionProbability (setup : List (Tx P)) (adv : Adversary P cap n) : ℝ :=
  (Pr[= true | do
    let hp ← $ᵗ (P.SpendKey → P.PubKey)
    let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
    let hc ← $ᵗ (Model.Table P cap)
    let d ← atDraws setup adv hp hn hc
    pure (collisionDraw setup adv hp hn hc d)]).toReal

theorem rejection_le_validity_add_collision (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) :
    rejectionProbability sup setup adv ≤ validityFailureProbability sup setup adv + collisionProbability setup adv := by
  classical
  let bad := fun d : Joint adv => d.2.2.2.1 = true
  let col := fun d : Joint adv => collisionDraw setup adv d.1 d.2.1 d.2.2.1 d.2.2.2.2 = true
  let rej := fun d : Joint adv => rejected sup adv d.1 d.2.1 d.2.2.1 d.2.2.2.2 = true
  have hm : Pr[rej | jointDraws sup setup adv] ≤ Pr[bad | jointDraws sup setup adv] + Pr[col | jointDraws sup setup adv] := by
    apply (probEvent_mono (q := fun d => bad d ∨ col d) ?_).trans (probEvent_or_le _ _ _)
    intro d hd
    simp only [jointDraws, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hd
    obtain ⟨hp,_,hn,_,hc,_,x,hx,rfl⟩ := hd
    exact joint_rejection_collision sup setup adv hp hn hc x hx
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
        (fun d => pure (rejected sup adv hp hn hc d))
  have hjc (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
      (hc : Model.Table P cap) := joint_forget sup setup adv hp hn hc
        (fun d => pure (collisionDraw setup adv hp hn hc d))
  simpa only [rej, bad, col, jointDraws, bind_assoc, pure_bind, hjr, hjc] using hr

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Fintype P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem collisionProbability_le (setup : List (Tx P)) (adv : Adversary P cap n)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    collisionProbability setup adv ≤
      (2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment := by
  have hb : (do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      let hc ← $ᵗ (Model.Table P cap)
      let d ← atDraws setup adv hp hn hc
      pure (collisionDraw setup adv hp hn hc d)).boolDistAdvantage (do
      let _hp ← $ᵗ (P.SpendKey → P.PubKey)
      let _hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      pure false) ≤
        (2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
          (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment := by
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro hp _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro hn _
    simpa [ProbComp.boolDistAdvantage, abs_of_nonneg ENNReal.toReal_nonneg] using
      atCollision_le setup adv hp hn qc qg hq
  simpa [collisionProbability, ProbComp.boolDistAdvantage, abs_of_nonneg ENNReal.toReal_nonneg] using hb

/-- Numeric ROM rejection charge, plus failure of the inherited deterministic validity class. -/
theorem advantage_le_rom_collisions (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      ((2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment +
        validityFailureProbability sup setup adv) / 2 := by
  have h := advantage_le_queryBound sup setup adv qc qg hq
  have hr := rejection_le_validity_add_collision sup setup adv
  have hc := collisionProbability_le setup adv qc qg hq
  linarith

end LeanShieldedPool.RecipientGame.ROMCommit
