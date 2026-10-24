import SenderGame.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.Toy
open WithdrawGame.Transport GameCorrespondence PrivacyTools

def swapKeys : Keys ≃ Keys where
  toFun := fun keys i => ((keys i).1, (keys i).2 ∘ Equiv.swap (0 : Fin 5) 1)
  invFun := fun keys i => ((keys i).1, (keys i).2 ∘ Equiv.swap (0 : Fin 5) 1)
  left_inv := by intro keys; funext i; apply Prod.ext; rfl; funext x; simp
  right_inv := by intro keys; funext i; apply Prod.ext; rfl; funext x; simp

theorem swap_inputs (keys : Keys) : InputsOK (swapKeys keys) ↔ InputsOK keys := by
  simp [InputsOK, swapKeys, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 5) ≠ 0)
    (by decide : (2 : Fin 5) ≠ 1), and_comm]

theorem swap_view (keys : Keys) (s₁ s₂ : Fin 5) :
    observerView (challenge.history (swapKeys keys) s₁ s₂ false) =
      observerView (challenge.history keys s₁ s₂ true) := by
  simp [Challenge.history, Challenge.world, World.transfer, challenge, world, note,
    Output.note, WithdrawGame.NotePlan.resolve, WithdrawGame.Intent.resolve, observerView, events,
    gameEvent, Tx.event, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm, Prim,
    swapKeys, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 5) ≠ 0) (by decide : (2 : Fin 5) ≠ 1)]

noncomputable def guardedGuess (g : (Unit → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool)
    (keys : Keys) (s₁ s₂ : Fin 5) (b : Bool) : ProbComp Bool :=
  if InputsOK keys ∧ OutputsOK s₁ s₂ then
    g (Prim.derivePub ∘ keys) (observerView (challenge.history keys s₁ s₂ b))
  else $ᵗ Bool

noncomputable def guardedBranch (g : (Unit → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool)
    (b : Bool) : ProbComp Bool := do
  let keys ← $ᵗ Keys
  let s₁ ← $ᵗ (Fin 5)
  let s₂ ← $ᵗ (Fin 5)
  guardedGuess g keys s₁ s₂ b

theorem branches_equal (g) :
    Pr[= true | guardedBranch g true] = Pr[= true | guardedBranch g false] := by
  have h := probOutput_bind_bijective_uniform_cross Keys swapKeys swapKeys.bijective
    (fun keys => do
      let s₁ ← $ᵗ (Fin 5)
      let s₂ ← $ᵗ (Fin 5)
      guardedGuess g keys s₁ s₂ false) true
  have he (keys : Keys) (s₁ s₂ : Fin 5) :
      guardedGuess g (swapKeys keys) s₁ s₂ false = guardedGuess g keys s₁ s₂ true := by
    simp only [guardedGuess, swap_inputs, swap_view]
    rfl
  simpa only [he, guardedBranch] using h

theorem experiment_coin (g) :
    𝒮[SenderGame.experiment (fun _ => True) (adversary g)] =
      𝒮[PrivacyTools.coin (guardedBranch g)] := by
  have hfixed (keys : Keys) (s₁ s₂ : Fin 5) (b : Bool) :
      𝒮[SenderGame.challengeExp (fun _ => True) (adversary g) keys challenge () s₁ s₂ b] =
      𝒮[do let z ← guardedGuess g keys s₁ s₂ b; pure (b == z)] := by
    by_cases h : SenderGame.Legal (fun _ => True) keys challenge s₁ s₂
    · simp only [SenderGame.challengeExp, if_pos h, legal_guarded_log _ _ _ _ _ h b,
        guardedGuess, (legal_iff keys s₁ s₂).mp h, and_self, if_true, adversary]
    · have hn : ¬ (InputsOK keys ∧ OutputsOK s₁ s₂) := by simpa only [legal_iff] using h
      apply evalSPMF_ext
      intro x
      cases b <;> cases x <;> simp [SenderGame.challengeExp, h, guardedGuess, hn]
  simp only [SenderGame.experiment, SenderGame.draws, adversary, bind_assoc, pure_bind,
    PrivacyTools.coin, guardedBranch]
  calc
    _ = 𝒮[do
      let keys ← $ᵗ Keys
      let s₁ ← $ᵗ (Fin 5)
      let s₂ ← $ᵗ (Fin 5)
      let b ← $ᵗ Bool
      let z ← guardedGuess g keys s₁ s₂ b
      pure (b == z)] := by
      apply evalSPMF_bind_congr_left
      intro keys
      apply evalSPMF_bind_congr_left
      intro s₁
      apply evalSPMF_bind_congr_left
      intro s₂
      apply evalSPMF_bind_congr_left
      intro b
      exact hfixed keys s₁ s₂ b
    _ = _ := by
      have h := evalSPMF_bind_comm
        (do let keys ← $ᵗ Keys; let s₁ ← $ᵗ (Fin 5); let s₂ ← $ᵗ (Fin 5); pure (keys, s₁, s₂))
        ($ᵗ Bool) (fun a b => do let z ← guardedGuess g a.1 a.2.1 a.2.2 b; pure (b == z))
      simpa only [bind_assoc, pure_bind] using h

/-- The symmetric two-candidate schedule has zero bias for every observer without a key. -/
theorem toy_without_key_zero (g) : SenderGame.advantage (fun _ => True) (adversary g) = 0 := by
  unfold SenderGame.advantage
  rw [OracleComp.probOutput_congr (x := true) rfl (experiment_coin g), coin_bias]
  simp [ProbComp.boolDistAdvantage, branches_equal]

def leakedGuess (key : Prim.SpendKey) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .transfer nf _ _ _] => !(nf == key.2 0)
  | _ => false

/-- The same key, salt draws, challenge, and guards; one sampled spending key reaches guess. -/
noncomputable def leakedExperiment : ProbComp Bool := do
  let keys ← $ᵗ Keys
  let s₁ ← $ᵗ (Fin 5)
  let s₂ ← $ᵗ (Fin 5)
  let b ← $ᵗ Bool
  SenderGame.challengeExp (fun _ => True)
    (adversary (fun _ log => pure (leakedGuess (keys ()) log))) keys challenge () s₁ s₂ b

theorem leaked_guess_eq (keys : Keys) (s₁ s₂ : Fin 5) (b : Bool) :
    leakedGuess (keys ()) (observerView (challenge.history keys s₁ s₂ b)) =
      (b && !((keys ()).2 1 == (keys ()).2 0)) := by
  cases b <;> simp [leakedGuess, Challenge.history, Challenge.world, World.transfer,
    challenge, world, note, Output.note, WithdrawGame.NotePlan.resolve, WithdrawGame.Intent.resolve,
    observerView, events, gameEvent, Tx.event, TransferData.nf1, Note.nf, Note.cm, Prim]

def Distinct (keys : Keys) : Prop := InputsOK keys ∧ (keys ()).2 1 ≠ (keys ()).2 0
instance (keys : Keys) : Decidable (Distinct keys) := by unfold Distinct; infer_instance

theorem distinct_probability : Pr[Distinct | $ᵗ Keys] = 3/8 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter Distinct).card = 768 := by decide
  have ht : Fintype.card Keys = 2048 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num


theorem leaked_round (keys : Keys) (s₁ s₂ : Fin 5) :
    Pr[= true | do
      let b ← $ᵗ Bool
      SenderGame.challengeExp (fun _ => True)
        (adversary (fun _ log => pure (leakedGuess (keys ()) log))) keys challenge () s₁ s₂ b] =
      if Distinct keys ∧ OutputsOK s₁ s₂ then 1 else 1/2 := by
  by_cases h : InputsOK keys ∧ OutputsOK s₁ s₂
  · have hl := (legal_iff keys s₁ s₂).mpr h
    have he (b : Bool) : SenderGame.challengeExp (fun _ => True)
        (adversary (fun _ log => pure (leakedGuess (keys ()) log))) keys challenge () s₁ s₂ b =
        pure (b == (b && !((keys ()).2 1 == (keys ()).2 0))) := by
      simp only [SenderGame.challengeExp, if_pos hl, legal_guarded_log _ _ _ _ _ hl b,
        adversary, pure_bind, leaked_guess_eq]
    simp only [he, probOutput_bind_eq_sum_fintype, Fintype.sum_bool]
    by_cases hn : (keys ()).2 1 = (keys ()).2 0 <;>
      simp [Distinct, h.1, h.2, hn, ENNReal.inv_two_add_inv_two]
  · have hl : ¬ SenderGame.Legal (fun _ => True) keys challenge s₁ s₂ := by
      simpa only [legal_iff] using h
    have hd : ¬ (Distinct keys ∧ OutputsOK s₁ s₂) := by
      unfold Distinct
      tauto
    simp [SenderGame.challengeExp, hl, hd]

/-- One disclosed key changes the zero-bias baseline to exactly 9/200. -/
theorem toy_with_one_key_bias : |(Pr[= true | leakedExperiment]).toReal - 1/2| = 9/200 := by
  let d : ProbComp (Keys × Fin 5 × Fin 5) := do
    let keys ← $ᵗ Keys
    let s₁ ← $ᵗ (Fin 5)
    let s₂ ← $ᵗ (Fin 5)
    pure (keys, s₁, s₂)
  let p : Keys × Fin 5 × Fin 5 → Prop := fun a => Distinct a.1 ∧ OutputsOK a.2.1 a.2.2
  have he : Pr[= true | leakedExperiment] =
      Pr[= true | do let a ← d; if p a then pure true else $ᵗ Bool] := by
    simp only [leakedExperiment, d, p, bind_assoc, pure_bind]
    apply probOutput_bind_congr
    intro keys _
    apply probOutput_bind_congr
    intro s₁ _
    apply probOutput_bind_congr
    intro s₂ _
    rw [leaked_round]
    split_ifs <;> simp
  have ho : Pr[fun ss : Fin 5 × Fin 5 => OutputsOK ss.1 ss.2 | do
      let s₁ ← $ᵗ (Fin 5); let s₂ ← $ᵗ (Fin 5); pure (s₁, s₂)] = 6/25 := by
    rw [← decide_probability]
    simpa only [bind_assoc, pure_bind] using output_probability
  have hp : (Pr[p | d]).toReal = 9/100 := by
    rw [← decide_probability]
    simp only [d, p, bind_assoc, pure_bind]
    have h := independent_and ($ᵗ Keys)
      (do let s₁ ← $ᵗ (Fin 5); let s₂ ← $ᵗ (Fin 5); pure (s₁, s₂))
      Distinct (fun ss => OutputsOK ss.1 ss.2)
    simp only [bind_assoc, pure_bind] at h
    rw [h, distinct_probability, ho]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  rw [he, pure_or_fair_probability, hp]
  norm_num

theorem toy_key_disclosure_changes_bias (g) :
    SenderGame.advantage (fun _ => True) (adversary g) = 0 ∧
    |(Pr[= true | leakedExperiment]).toReal - 1/2| = 9/200 :=
  ⟨toy_without_key_zero g, toy_with_one_key_bias⟩

end LeanShieldedPool.SenderGame.Toy
