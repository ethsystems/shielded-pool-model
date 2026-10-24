import PrivacyTools.Rejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.SenderGame.Toy
open WithdrawGame WithdrawGame.Transport GameCorrespondence PrivacyTools

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool × (Fin 5 → Fin 4)
  Salt := Fin 5
  Commitment := Fin 5
  Nullifier := Fin 4
  derivePub := Prod.fst
  commit := fun _ _ _ salt => salt
  nullify := fun cm key => key.2 cm

abbrev Keys := Unit → Prim.SpendKey

def note (s : Fin 5) (a : Nat := 1) : NotePlan Prim Unit := ⟨(), a, (), s⟩

def world (s : Fin 5) : World Prim Unit :=
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

def OutputsOK (s₁ s₂ : Fin 5) : Prop := s₁ ≠ 0 ∧ s₁ ≠ 1 ∧ s₂ ≠ 0 ∧ s₂ ≠ 1 ∧ s₁ ≠ s₂

def InputsOK (keys : Keys) : Prop := (keys ()).2 0 ≠ (keys ()).2 2 ∧ (keys ()).2 1 ≠ (keys ()).2 2

instance (s₁ s₂ : Fin 5) : Decidable (OutputsOK s₁ s₂) := by
  unfold OutputsOK
  infer_instance
instance (keys : Keys) : Decidable (InputsOK keys) := by
  unfold InputsOK
  infer_instance

theorem guard_iff (keys : Keys) (s₁ s₂ : Fin 5) (b : Bool) :
    ((challenge.world b).transfer keys s₁ s₂ challenge.snapshot).guard (priorState keys) ↔
      (keys ()).2 (if b then 1 else 0) ≠ (keys ()).2 2 ∧ OutputsOK s₁ s₂ := by
  cases b <;>
    norm_num [TransferData.guard, World.transfer, Challenge.world, challenge, world,
      priorState, afterFirst, DepositData.post, NotePlan.resolve, note, Output.note,
      St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy,
      Note.isBallast, St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2,
      Note.nf, Note.cm, Prim, U128, maxU128, OutputsOK, ne_comm]
  all_goals tauto

theorem legal_iff (keys : Keys) (s₁ s₂ : Fin 5) :
    SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ ↔ InputsOK keys ∧ OutputsOK s₁ s₂ := by
  constructor
  · rintro ⟨_, _, _, _, _, _, _, _, _, _, st, hs, _, _, hl, hr⟩
    rw [RecipientGame.runChecked_complete (prefix_run keys)] at hs
    cases hs
    have hl' := (guard_iff keys s₁ s₂ false).mp hl
    have hr' := (guard_iff keys s₁ s₂ true).mp hr
    exact ⟨⟨hl'.1, hr'.1⟩, hl'.2⟩
  · rintro ⟨hi, ho⟩
    refine ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, by change (0 : Fin 5) ≠ 1; decide,
      priorState keys, RecipientGame.runChecked_complete (prefix_run keys), ?_, ?_,
      (guard_iff keys s₁ s₂ false).mpr ⟨hi.1, ho⟩,
      (guard_iff keys s₁ s₂ true).mpr ⟨hi.2, ho⟩⟩ <;>
      simp [priorState, afterFirst, DepositData.post, St.empty, challenge, world]

theorem toy_key_dependence :
    Prim.derivePub (false, fun _ => 0) = Prim.derivePub (false, fun _ => 1) ∧
    Prim.nullify 0 (false, fun _ => 0) ≠ Prim.nullify 0 (false, fun _ => 1) := by decide

theorem toy_hiding : OwnerGame.Hiding (P := Prim) 0 := by
  intro t a pk t' a' pk' test
  simp [ProbComp.boolDistAdvantage, Prim]

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

theorem input_probability : Pr[InputsOK | $ᵗ Keys] = 9/16 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter InputsOK).card = 1152 := by decide
  have ht : Fintype.card Keys = 2048 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem coordinate_collision : Pr[fun keys : Keys => (keys ()).2 0 = (keys ()).2 2 | $ᵗ Keys] = 1/4 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun keys : Keys => (keys ()).2 0 = (keys ()).2 2)).card = 512 := by decide
  have ht : Fintype.card Keys = 2048 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem output_probability : Pr[= true | do
    let s₁ ← $ᵗ (Fin 5)
    let s₂ ← $ᵗ (Fin 5)
    pure (decide (OutputsOK s₁ s₂))] = 6/25 := by
  rw [probOutput_bind_eq_sum_fintype]
  simp only [probOutput_bind_eq_sum_fintype, probOutput_uniformSample,
    Fintype.card_fin, probOutput_pure]
  simp only [Fin.sum_univ_succ]
  norm_num [OutputsOK, Fin.ext_iff]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_inv]

theorem toy_rejection (g) : SenderGame.rejectionProbability (fun _ => True) (adversary g) = 173/200 := by
  classical
  have hp : Pr[= true | do
      let keys ← $ᵗ Keys
      let s₁ ← $ᵗ (Fin 5)
      let s₂ ← $ᵗ (Fin 5)
      pure (decide (InputsOK keys ∧ OutputsOK s₁ s₂))] = 27/200 := by
    have he (keys : Keys) : Pr[= true | do
        let s₁ ← $ᵗ (Fin 5)
        let s₂ ← $ᵗ (Fin 5)
        pure (decide (InputsOK keys ∧ OutputsOK s₁ s₂))] =
        if InputsOK keys then 6/25 else 0 := by
      by_cases h : InputsOK keys
      · simp only [h, true_and, if_true]
        exact output_probability
      · simp [h]
    rw [probOutput_bind_eq_tsum]
    simp only [he]
    have hm (keys : Keys) : Pr[= keys | $ᵗ Keys] * (if InputsOK keys then 6/25 else 0) =
        (if InputsOK keys then Pr[= keys | $ᵗ Keys] else 0) * (6/25) := by
      by_cases h : InputsOK keys <;> simp [h]
    simp_rw [hm]
    rw [ENNReal.tsum_mul_right]
    have hi : (∑' keys : Keys, if InputsOK keys then Pr[= keys | $ᵗ Keys] else 0) = 9/16 := by
      simpa only [probEvent_eq_tsum_ite] using input_probability
    rw [hi]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  have he : Pr[= true | do
      let (keys, c, _, s₁, s₂, _) ← SenderGame.draws (adversary g)
      pure (decide (¬ SenderGame.Legal (fun _ => True) keys c s₁ s₂))] =
      Pr[= true | Bool.not <$> (do
        let keys ← $ᵗ Keys
        let s₁ ← $ᵗ (Fin 5)
        let s₂ ← $ᵗ (Fin 5)
        pure (decide (InputsOK keys ∧ OutputsOK s₁ s₂)))] := by
    simp only [SenderGame.draws, adversary, bind_assoc, pure_bind, legal_iff, map_bind, map_pure]
    apply probOutput_bind_congr
    intro keys _
    apply probOutput_bind_congr
    intro s₁ _
    apply probOutput_bind_congr
    intro s₂ _
    simp [or_assoc]
  unfold SenderGame.rejectionProbability
  rw [he, probOutput_not_map, probOutput_false_eq_sub, hp]
  simp only [probFailure_eq_zero, tsub_zero]
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.div_le_iff (by norm_num) (by finiteness)).2
    norm_num) (by finiteness)]
  norm_num [ENNReal.toReal_div]

theorem toy_positive_with_collisions (g) :
    SenderGame.advantage (fun _ => True) (adversary g) ≤ 173/400 := by
  have h := SenderGame.advantage_le (fun _ => True) (adversary g) 0 0
    toy_multi_key_prf (by norm_num) toy_hiding
  rw [toy_rejection] at h
  linarith


theorem prefix_not_rejected (keys : Keys) : ¬ SenderGame.PrefixRejected (fun _ => True) keys challenge := by
  simp [SenderGame.PrefixRejected, RecipientGame.runChecked_complete (prefix_run keys)]

theorem input_collision_iff (keys : Keys) (s₁ s₂ : Fin 5) :
    SenderGame.InputCollision (fun _ => True) keys challenge s₁ s₂ ↔ ¬ InputsOK keys := by
  unfold SenderGame.InputCollision
  rw [RecipientGame.runChecked_complete (prefix_run keys)]
  simp [Challenge.world, World.transfer, challenge, world, note, WithdrawGame.NotePlan.resolve,
    priorState, afterFirst, DepositData.post, St.empty, TransferData.nf1, TransferData.nf2,
    Note.nf, Note.cm, Prim, InputsOK]
  tauto

theorem output_collision_iff (keys : Keys) (s₁ s₂ : Fin 5) :
    SenderGame.OutputCollision (fun _ => True) keys challenge s₁ s₂ ↔ ¬ OutputsOK s₁ s₂ := by
  unfold SenderGame.OutputCollision
  rw [RecipientGame.runChecked_complete (prefix_run keys)]
  simp [Challenge.world, World.transfer, challenge, world, note, Output.note, WithdrawGame.NotePlan.resolve,
    priorState, afterFirst, DepositData.post, St.empty, St.leaves, Note.cm, Prim, OutputsOK, eq_comm]
  tauto

theorem toy_prefix_term_zero (g) : (SenderGame.terms (fun _ => True) (adversary g)).1 = 0 := by
  simp [SenderGame.terms, SenderGame.draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, prefix_not_rejected]

theorem toy_other_term_zero (g) : (SenderGame.terms (fun _ => True) (adversary g)).2.2.2 = 0 := by
  have hn (keys : Keys) (s₁ s₂ : Fin 5) :
      (¬ SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ ∧
       ¬ SenderGame.PrefixRejected (fun _ => True) keys challenge ∧
       ¬ SenderGame.InputCollision (fun _ => True) keys challenge s₁ s₂ ∧
       ¬ SenderGame.OutputCollision (fun _ => True) keys challenge s₁ s₂) ↔ False := by
    rw [legal_iff, input_collision_iff, output_collision_iff]
    tauto
  simp [SenderGame.terms, SenderGame.draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, hn]

theorem toy_input_collision_term (g) : (SenderGame.terms (fun _ => True) (adversary g)).2.1 = 7/16 := by
  classical
  have hn (keys : Keys) (s₁ s₂ : Fin 5) :
      (¬ SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ ∧
       ¬ SenderGame.PrefixRejected (fun _ => True) keys challenge ∧
       SenderGame.InputCollision (fun _ => True) keys challenge s₁ s₂) ↔ ¬ InputsOK keys := by
    rw [legal_iff, input_collision_iff]
    have h := prefix_not_rejected keys
    tauto
  have he : (SenderGame.terms (fun _ => True) (adversary g)).2.1 =
      (Pr[fun keys => ¬InputsOK keys | $ᵗ Keys]).toReal := by
    change (Pr[fun a => ¬SenderGame.Legal (fun _ => True) a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1 ∧
      ¬SenderGame.PrefixRejected (fun _ => True) a.1 a.2.1 ∧
      SenderGame.InputCollision (fun _ => True) a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1 | SenderGame.draws (adversary g)]).toReal = _
    congr 1
    rw [← decide_probability, ← decide_probability]
    simp only [SenderGame.draws, adversary, bind_assoc, pure_bind, hn]
    apply probOutput_bind_congr
    intro keys _
    simp
  rw [he]
  have hc := congrArg ENNReal.toReal (probEvent_compl ($ᵗ Keys) InputsOK)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), input_probability] at hc
  norm_num only [probFailure_eq_zero, tsub_zero, ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hc
  linarith

theorem toy_output_collision_term (g) : (SenderGame.terms (fun _ => True) (adversary g)).2.2.1 = 171/400 := by
  have h := SenderGame.rejection_partition (fun _ => True) (adversary g)
  rw [toy_rejection, toy_prefix_term_zero, toy_input_collision_term, toy_other_term_zero] at h
  linarith

end LeanShieldedPool.SenderGame.Toy
