import SenderGame.Disclosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.SenderGame.DropPRF
open WithdrawGame WithdrawGame.Transport GameCorrespondence PrivacyTools

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool
  Salt := Fin 16
  Commitment := Fin 16
  Nullifier := Bool × Fin 16
  derivePub := id
  commit := fun _ _ _ salt => salt
  nullify := fun cm key => (key, cm)

abbrev Keys := Unit → Prim.SpendKey

def note (s : Fin 16) (a : Nat := 1) : NotePlan Prim Unit := ⟨(), a, (), s⟩

def world (s : Fin 16) : World Prim Unit :=
  ⟨note s, note 2 0, ⟨(), 1, ()⟩, ⟨(), 0, ()⟩⟩

def challenge : SenderGame.Challenge Prim Unit where
  prior := [.deposit (note 0) (), .deposit (note 1) ()]
  left := world 0
  right := world 1
  snapshot := 2

def adversary (g : (Unit → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool) :
    SenderGame.Adversary Prim Unit where
  State := Unit
  choose := fun _ => pure (challenge, ())
  guess := fun _ => g

noncomputable def afterFirst (keys : Keys) : St Prim :=
  (DepositData.mk ((note 0).resolve keys) ()).post (St.empty Prim (fun _ => True))
noncomputable def priorState (keys : Keys) : St Prim :=
  (DepositData.mk ((note 1).resolve keys) ()).post (afterFirst keys)

theorem first_guard (keys : Keys) :
    (DepositData.mk ((note 0).resolve keys) ()).guard (St.empty Prim (fun _ => True)) := by
  norm_num [DepositData.guard, NotePlan.resolve, note, St.empty, St.leaves, U128, maxU128]

theorem second_guard (keys : Keys) :
    (DepositData.mk ((note 1).resolve keys) ()).guard (afterFirst keys) := by
  norm_num [DepositData.guard, afterFirst, DepositData.post, NotePlan.resolve, note,
    St.empty, St.leaves, Note.cm, Prim, U128, maxU128]

theorem prefix_run (keys : Keys) :
    Run (fun _ => True) (challenge.prior.map (Intent.resolve keys)) (priorState keys) :=
  Run.step (Run.step Run.empty (Step.deposit (first_guard keys))) (Step.deposit (second_guard keys))

def OutputsOK (s₁ s₂ : Fin 16) : Prop := s₁ ≠ 0 ∧ s₁ ≠ 1 ∧ s₂ ≠ 0 ∧ s₂ ≠ 1 ∧ s₁ ≠ s₂

def InputsOK (_keys : Keys) : Prop := True

instance (s₁ s₂ : Fin 16) : Decidable (OutputsOK s₁ s₂) := by
  unfold OutputsOK
  infer_instance
instance (keys : Keys) : Decidable (InputsOK keys) := isTrue trivial

theorem guard_iff (keys : Keys) (s₁ s₂ : Fin 16) (b : Bool) :
    ((challenge.world b).transfer keys s₁ s₂ challenge.snapshot).guard (priorState keys) ↔
      True ∧ OutputsOK s₁ s₂ := by
  cases b <;>
    norm_num [TransferData.guard, World.transfer, Challenge.world, challenge, world,
      priorState, afterFirst, DepositData.post, NotePlan.resolve, note, Output.note,
      St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy,
      Note.isBallast, St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2,
      Note.nf, Note.cm, Prim, U128, maxU128, OutputsOK, ne_comm]
  all_goals simp only [Prod.mk.injEq, true_and]
  all_goals tauto

theorem legal_iff (keys : Keys) (s₁ s₂ : Fin 16) :
    SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ ↔ InputsOK keys ∧ OutputsOK s₁ s₂ := by
  constructor
  · rintro ⟨_, _, _, _, _, _, _, _, _, _, st, hs, _, _, hl, hr⟩
    rw [RecipientGame.runChecked_complete (prefix_run keys)] at hs
    cases hs
    have hl' := (guard_iff keys s₁ s₂ false).mp hl
    have hr' := (guard_iff keys s₁ s₂ true).mp hr
    exact ⟨trivial, hl'.2⟩
  · rintro ⟨hi, ho⟩
    refine ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, by change (0 : Fin 16) ≠ 1; decide,
      priorState keys, RecipientGame.runChecked_complete (prefix_run keys), ?_, ?_,
      (guard_iff keys s₁ s₂ false).mpr ⟨trivial, ho⟩,
      (guard_iff keys s₁ s₂ true).mpr ⟨trivial, ho⟩⟩ <;>
      simp [priorState, afterFirst, DepositData.post, St.empty, challenge, world]

theorem toy_hiding : OwnerGame.Hiding (P := Prim) 0 := by
  intro t a pk t' a' pk' test
  simp [ProbComp.boolDistAdvantage, Prim]

theorem toy_key_dependence : Prim.nullify 0 false ≠ Prim.nullify 0 true := by decide

def guess : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .transfer nf _ _ _] => nf.2 == 1
  | _ => false

def attacker : SenderGame.Adversary Prim Unit := adversary (fun _ log => pure (guess log))

theorem guess_eq (keys : Keys) (s₁ s₂ : Fin 16) (b : Bool) :
    guess (observerView (challenge.history keys s₁ s₂ b)) = b := by
  cases b <;> simp [guess, Challenge.history, Challenge.world, World.transfer,
    challenge, world, note, Output.note, WithdrawGame.NotePlan.resolve, WithdrawGame.Intent.resolve,
    observerView, events, gameEvent, Tx.event, TransferData.nf1, Note.nf, Note.cm, Prim]

noncomputable def salts : ProbComp (Fin 16 × Fin 16) := do
  let s₁ ← $ᵗ (Fin 16)
  let s₂ ← $ᵗ (Fin 16)
  pure (s₁, s₂)

theorem salts_uniform : salts = $ᵗ (Fin 16 × Fin 16) := by rfl

theorem output_probability : Pr[fun ss => OutputsOK ss.1 ss.2 | salts] = 91/128 := by
  rw [salts_uniform, probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun ss : Fin 16 × Fin 16 => OutputsOK ss.1 ss.2)).card = 182 := by decide
  have ht : Fintype.card (Fin 16 × Fin 16) = 256 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem challenge_probability (keys : Keys) (s₁ s₂ : Fin 16) (b : Bool) :
    Pr[= true | SenderGame.challengeExp (fun _ => True) attacker keys challenge () s₁ s₂ b] =
      if OutputsOK s₁ s₂ then 1 else 1/2 := by
  by_cases h : OutputsOK s₁ s₂
  · have hl := (legal_iff keys s₁ s₂).mpr ⟨trivial, h⟩
    simp only [SenderGame.challengeExp, if_pos hl, legal_guarded_log _ _ _ _ _ hl b,
      attacker, adversary, pure_bind, guess_eq, beq_self_eq_true, if_pos h]
    simp
  · have hl : ¬ SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ := by
      simp [legal_iff, h]
    simp [SenderGame.challengeExp, hl, h]

theorem experiment_probability : (Pr[= true | SenderGame.experiment (fun _ => True) attacker]).toReal =
    1/2 + (91/128 : ℝ)/2 := by
  have he : Pr[= true | SenderGame.experiment (fun _ => True) attacker] =
      Pr[= true | do let ss ← salts; if OutputsOK ss.1 ss.2 then pure true else $ᵗ Bool] := by
    simp only [SenderGame.experiment, SenderGame.draws, attacker, adversary, bind_assoc, pure_bind]
    rw [probOutput_bind_of_const ($ᵗ Keys) (r := Pr[= true | do
      let ss ← salts
      if OutputsOK ss.1 ss.2 then pure true else $ᵗ Bool])]
    · simp
    · intro keys _
      simp only [salts, bind_assoc, pure_bind]
      apply probOutput_bind_congr
      intro s₁ _
      apply probOutput_bind_congr
      intro s₂ _
      change Pr[= true | do let b ← $ᵗ Bool; SenderGame.challengeExp (fun _ => True) attacker keys challenge () s₁ s₂ b] = _
      rw [probOutput_bind_of_const ($ᵗ Bool) (r := if OutputsOK s₁ s₂ then 1 else 1/2)
        (fun b _ => challenge_probability keys s₁ s₂ b)]
      split_ifs <;> simp
  rw [he, pure_or_fair_probability, output_probability]
  norm_num [ENNReal.toReal_div]

theorem toy_advantage : SenderGame.advantage (fun _ => True) attacker = 91/256 := by
  unfold SenderGame.advantage
  rw [experiment_probability]
  norm_num

theorem toy_rejection : SenderGame.rejectionProbability (fun _ => True) attacker = 37/128 := by
  classical
  have he : Pr[= true | do
      let (keys, c, _, s₁, s₂, _) ← SenderGame.draws attacker
      pure (decide (¬ SenderGame.Legal (fun _ => True) keys c s₁ s₂))] =
      Pr[= true | Bool.not <$> (do let ss ← salts; pure (decide (OutputsOK ss.1 ss.2)))] := by
    simp only [SenderGame.draws, attacker, adversary, bind_assoc, pure_bind, legal_iff, InputsOK,
      true_and, map_bind, map_pure, salts]
    rw [probOutput_bind_of_const ($ᵗ Keys) (r := Pr[= true | do
      let s₁ ← $ᵗ (Fin 16)
      let s₂ ← $ᵗ (Fin 16)
      pure (!decide (OutputsOK s₁ s₂))])]
    · simp
    · intro keys _
      apply probOutput_bind_congr
      intro s₁ _
      apply probOutput_bind_congr
      intro s₂ _
      simp
  unfold SenderGame.rejectionProbability
  rw [he, probOutput_not_map, probOutput_false_eq_sub, decide_probability, output_probability]
  simp only [probFailure_eq_zero, tsub_zero]
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.div_le_iff (by norm_num) (by finiteness)).2
    norm_num) (by finiteness)]
  norm_num [ENNReal.toReal_div]

/-- Hiding still holds at zero error; omitting the joint PRF premise falsifies its bound. -/
theorem toy_drop_premise : ¬ SenderGame.advantage (fun _ => True) attacker ≤
    (0 : ℝ) + 0 + SenderGame.rejectionProbability (fun _ => True) attacker / 2 := by
  rw [toy_advantage, toy_rejection]
  norm_num

theorem toy_joint_premise_fails : ¬ MultiKeyPublicKeyPRF (P := Prim) (ι := Unit) 0 := by
  intro h
  exact toy_drop_premise (SenderGame.advantage_le (fun _ => True) attacker 0 0 h (by norm_num) toy_hiding)

end LeanShieldedPool.SenderGame.DropPRF
