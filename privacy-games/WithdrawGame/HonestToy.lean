import WithdrawGame.RejectionTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.HonestToy
open GameCorrespondence Transport

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool × (Fin 3 → Fin 4)
  Salt := Fin 3
  Commitment := Fin 3
  Nullifier := Fin 4
  derivePub := Prod.fst
  commit := fun _ _ _ s => s
  nullify := fun cm k => k.2 cm

abbrev Keys := Unit → Prim.SpendKey

def note (s : Fin 3) : NotePlan Prim Unit := ⟨(), 1, (), s⟩

def challenge : Challenge Prim Unit where
  prior := [.deposit (note 0) (), .deposit (note 1) (), .deposit (note 2) (),
    .withdraw (note 0) () 3]
  left := note 1
  right := note 2
  recipient := ()
  snapshot := 3

def adversary (g : (Unit → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool) :
    Adversary Prim Unit where
  State := Unit
  choose := fun _ => pure (challenge, ())
  guess := fun _ => g

noncomputable def afterFirst (keys : Keys) : St Prim :=
  (DepositData.mk ((note 0).resolve keys) ()).post (St.empty Prim (fun _ => True))
noncomputable def afterSecond (keys : Keys) : St Prim :=
  (DepositData.mk ((note 1).resolve keys) ()).post (afterFirst keys)
noncomputable def afterThird (keys : Keys) : St Prim :=
  (DepositData.mk ((note 2).resolve keys) ()).post (afterSecond keys)
noncomputable def afterPrior (keys : Keys) : St Prim :=
  (WithdrawData.mk (keys ()) ((note 0).resolve keys) () 3).post (afterThird keys)

theorem first_guard (keys : Keys) :
    (DepositData.mk ((note 0).resolve keys) ()).guard (St.empty Prim (fun _ => True)) := by
  norm_num [DepositData.guard, NotePlan.resolve, note, St.empty, St.leaves, U128, maxU128]

theorem second_guard (keys : Keys) :
    (DepositData.mk ((note 1).resolve keys) ()).guard (afterFirst keys) := by
  norm_num [DepositData.guard, afterFirst, DepositData.post, NotePlan.resolve, note,
    St.empty, St.leaves, Note.cm, Prim, U128, maxU128]

theorem third_guard (keys : Keys) :
    (DepositData.mk ((note 2).resolve keys) ()).guard (afterSecond keys) := by
  norm_num [DepositData.guard, afterSecond, afterFirst, DepositData.post, NotePlan.resolve,
    note, St.empty, St.leaves, Note.cm, Prim, U128, maxU128]
  decide

theorem prior_withdraw_guard (keys : Keys) :
    (WithdrawData.mk (keys ()) ((note 0).resolve keys) () 3).guard (afterThird keys) := by
  norm_num [WithdrawData.guard, afterThird, afterSecond, afterFirst,
    DepositData.post, NotePlan.resolve, note, St.rootInWindow, St.pushWindow, rootWindow,
    St.empty, Note.ownedBy, St.inTreeAt, St.leaves, St.fresh, WithdrawData.nf,
    Note.nf, Note.cm, Prim, U128, maxU128, bump]

theorem prefix_run (keys : Keys) :
    Run (fun _ => True) (challenge.prior.map (Intent.resolve keys)) (afterPrior keys) :=
  Run.step (Run.step (Run.step (Run.step Run.empty (Step.deposit (first_guard keys)))
    (Step.deposit (second_guard keys))) (Step.deposit (third_guard keys)))
    (Step.withdraw (prior_withdraw_guard keys))

theorem candidate_guard (keys : Keys) (b : Bool) :
    (challenge.withdrawal keys b).guard (afterPrior keys) ↔
      (keys ()).2 (if b then 2 else 1) ≠ (keys ()).2 0 := by
  cases b <;>
    norm_num [WithdrawData.guard, Challenge.withdrawal, challenge, afterPrior, afterThird,
      afterSecond, afterFirst, WithdrawData.post, DepositData.post, NotePlan.resolve,
      note, St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy,
      St.inTreeAt, St.leaves, St.fresh, WithdrawData.nf, Note.nf, Note.cm, Prim,
      U128, maxU128, bump, drop]

theorem legal_iff (keys : Keys) : Legal (fun _ => True) keys challenge ↔
    (keys ()).2 1 ≠ (keys ()).2 0 ∧ (keys ()).2 2 ≠ (keys ()).2 0 := by
  constructor
  · rintro ⟨_, _, _, st, hs, _, _, hl, hr⟩
    rw [RecipientGame.runChecked_complete (prefix_run keys)] at hs
    cases hs
    exact ⟨(candidate_guard keys false).mp hl, (candidate_guard keys true).mp hr⟩
  · rintro ⟨hl, hr⟩
    refine ⟨rfl, rfl, by change (1 : Fin 3) ≠ 2; decide, afterPrior keys,
      RecipientGame.runChecked_complete (prefix_run keys), ?_, ?_,
      (candidate_guard keys false).mpr hl, (candidate_guard keys true).mpr hr⟩ <;>
      simp [afterPrior, afterThird, afterSecond, afterFirst, WithdrawData.post,
        DepositData.post, St.empty, challenge]

theorem toy_hidden_key_dependence :
    Prim.derivePub (false, fun _ => 0) = Prim.derivePub (false, fun _ => 1) ∧
    Prim.nullify 1 (false, fun _ => 0) ≠ Prim.nullify 1 (false, fun _ => 1) := by decide

/-- Uniformly sampled coordinates collide with probability 1/4, despite fixed salts. -/
theorem toy_coordinate_collision :
    Pr[fun keys : Keys => (keys ()).2 1 = (keys ()).2 0 | $ᵗ Keys] = 1 / 4 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun keys : Keys => (keys ()).2 1 = (keys ()).2 0)).card = 32 := by decide
  have ht : Fintype.card Keys = 128 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem toy_rejection_probability (g) :
    rejectionProbability (fun _ => True) (adversary g) = 7 / 16 := by
  have hc : (Finset.univ.filter (fun keys : Keys =>
      ¬ ((keys ()).2 1 ≠ (keys ()).2 0 ∧ (keys ()).2 2 ≠ (keys ()).2 0))).card = 56 := by decide
  have ht : Fintype.card Keys = 128 := by decide
  have hp : Pr[fun keys : Keys =>
      ¬ ((keys ()).2 1 ≠ (keys ()).2 0 ∧ (keys ()).2 2 ≠ (keys ()).2 0) | $ᵗ Keys] = 7 / 16 := by
    rw [probEvent_uniformSample, hc, ht]
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
    norm_num
  simp only [rejectionProbability, adversary, pure_bind, rejected_eq_not_legal, legal_iff]
  simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  have hp' : Pr[= true | do
      let keys ← $ᵗ Keys
      pure (decide (¬ ((keys ()).2 1 ≠ (keys ()).2 0 ∧ (keys ()).2 2 ≠ (keys ()).2 0)))] = 7 / 16 := by
    rw [← probEvent_eq_eq_probOutput]
    change Pr[(fun z => z = true) | ($ᵗ Keys) >>= pure ∘
      (fun keys => decide (¬ ((keys ()).2 1 ≠ (keys ()).2 0 ∧ (keys ()).2 2 ≠ (keys ()).2 0)))] = _
    rw [probEvent_bind_pure_comp]
    simpa only [Function.comp_def, decide_eq_true_eq] using hp
  rw [hp']
  norm_num [ENNReal.toReal_div]


def splitKey : Keys ≃ ((Unit → Bool) × Table Prim Unit) where
  toFun := fun keys => (Prim.derivePub ∘ keys, realTable keys)
  invFun := fun af i => (af.1 i, fun cm => af.2 (i, cm))
  left_inv := by intro keys; rfl
  right_inv := by intro af; rfl

theorem split_sample (k : ((Unit → Bool) × Table Prim Unit) → ProbComp Bool) :
    Pr[= true | do let keys ← $ᵗ Keys; k (splitKey keys)] =
    Pr[= true | do let pk ← $ᵗ (Unit → Bool); let f ← $ᵗ (Table Prim Unit); k (pk, f)] := by
  rw [probOutput_bind_bijective_uniform_cross Keys splitKey splitKey.bijective]
  rfl

/-- The public part and hidden random table are independent; error is exactly zero. -/
theorem toy_multi_key_prf : MultiKeyPublicKeyPRF (P := Prim) (ι := Unit) 0 := by
  intro t
  have hr := split_sample (fun af => t af.1 af.2)
  have hi := split_sample (fun af => do let f ← $ᵗ (Table Prim Unit); t af.1 f)
  change |(Pr[= true | do let keys ← $ᵗ Keys; t (splitKey keys).1 (splitKey keys).2]).toReal -
    (Pr[= true | do let keys ← $ᵗ Keys; let f ← $ᵗ (Table Prim Unit); t (splitKey keys).1 f]).toReal| ≤ 0
  rw [hr, hi]
  have hd : Pr[= true | do
      let pk ← $ᵗ (Unit → Bool)
      let _ ← $ᵗ (Table Prim Unit)
      let f ← $ᵗ (Table Prim Unit)
      t pk f] = Pr[= true | do
      let pk ← $ᵗ (Unit → Bool)
      let f ← $ᵗ (Table Prim Unit)
      t pk f] := by
    apply probOutput_bind_congr
    intro pk _
    simp
  rw [hd]
  simp

/-- A checked WithdrawGame bound for every probabilistic observer of this mixed prefix.
The allowance 7/32 is half the exact candidate-versus-prior collision probability. -/
theorem toy_positive_with_collision (g) :
    advantage (fun _ => True) (adversary g) ≤ 7 / 32 := by
  have h := Transport.advantage_le (fun _ => True) (adversary g) 0 toy_multi_key_prf
  rw [toy_rejection_probability] at h
  linarith


theorem toy_candidate_collision_iff (keys : Keys) :
    CandidateCollision (fun _ => True) keys challenge ↔
      (keys ()).2 1 = (keys ()).2 0 ∨ (keys ()).2 2 = (keys ()).2 0 := by
  unfold CandidateCollision
  rw [RecipientGame.runChecked_complete (prefix_run keys)]
  simp [afterPrior, afterThird, afterSecond, afterFirst, WithdrawData.post, DepositData.post,
    St.empty, Challenge.withdrawal, challenge, note, NotePlan.resolve,
    WithdrawData.nf, Note.nf, Note.cm, Prim]

theorem toy_prefix_rejection_zero (g) :
    drawEventProbability (adversary g) (PrefixRejected (fun _ => True)) = 0 := by
  have h (keys : Keys) : ¬ PrefixRejected (fun _ => True) keys challenge := by
    simp [PrefixRejected, RecipientGame.runChecked_complete (prefix_run keys)]
  simp [drawEventProbability, draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, h]

theorem toy_other_illegality_zero (g) :
    drawEventProbability (adversary g) (OtherIllegal (fun _ => True)) = 0 := by
  have h (keys : Keys) : ¬ OtherIllegal (fun _ => True) keys challenge := by
    simp only [OtherIllegal, legal_iff, toy_candidate_collision_iff]
    tauto
  simp [drawEventProbability, draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, h]

theorem toy_candidate_collision_probability (g) :
    drawEventProbability (adversary g) (CandidateCollision (fun _ => True)) = 7 / 16 := by
  have h := rejection_probability_partition (fun _ => True) (adversary g)
  rw [toy_rejection_probability, toy_prefix_rejection_zero, toy_other_illegality_zero] at h
  linarith

end LeanShieldedPool.WithdrawGame.HonestToy
