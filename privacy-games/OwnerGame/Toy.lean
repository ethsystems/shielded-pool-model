import PrivacyTools.Rejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.OwnerGame.Toy
open WithdrawGame GameCorrespondence PrivacyTools

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool × (Bool → Bool)
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool
  derivePub := Prod.fst
  commit := fun _ _ pk salt => pk ^^ salt
  nullify := fun cm key => key.2 cm

abbrev Keys := Bool → Prim.SpendKey

theorem toy_key_dependence :
    Prim.derivePub (false, fun _ => false) = Prim.derivePub (false, fun _ => true) ∧
    Prim.nullify false (false, fun _ => false) ≠ Prim.nullify false (false, fun _ => true) := by decide

theorem toy_hiding : Hiding (P := Prim) 0 := by
  intro t a pk t' a' pk' test
  cases pk <;> cases pk' <;>
    simp [ProbComp.boolDistAdvantage, probOutput_bind_eq_sum_fintype, Fintype.sum_bool, Prim, add_comm]

def priorNote : NotePlan Prim Bool := ⟨(), 1, false, false⟩

def challenge : OwnerGame.Challenge Prim Bool where
  prior := [.deposit priorNote ()]
  token := ()
  amount := 1
  funding := ()
  left := false
  right := true

def adversary (g : (Bool → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool) :
    OwnerGame.Adversary Prim Bool where
  State := Unit
  choose := fun _ => pure (challenge, ())
  guess := fun _ => g

noncomputable def priorState (keys : Keys) : St Prim :=
  (DepositData.mk (priorNote.resolve keys) ()).post (St.empty Prim (fun _ => True))

theorem prefix_run (keys : Keys) :
    Run (fun _ => True) (challenge.prior.map (Intent.resolve keys)) (priorState keys) := by
  apply Run.step Run.empty
  apply Step.deposit
  norm_num [DepositData.guard, priorNote, NotePlan.resolve, St.empty, St.leaves, U128, maxU128]

theorem legal_iff (keys : Keys) (salt b : Bool) :
    OwnerGame.Legal (fun _ => True) keys challenge salt b ↔
      ((keys b).1 ^^ salt) ≠ (keys false).1 := by
  unfold OwnerGame.Legal
  rw [RecipientGame.runChecked_complete (prefix_run keys)]
  simp only [Option.some.injEq, exists_eq_left]
  cases b <;> norm_num [DepositData.guard, Challenge.deposit, challenge, priorState,
    DepositData.post, priorNote, NotePlan.resolve, St.empty, St.leaves, Note.cm, Prim, U128, maxU128, ne_comm]

/-- One existing commitment leaves a collision probability of exactly one half. -/
theorem toy_rejection (g) : rejectionProbability (fun _ => True) (adversary g) = 1/2 := by
  have hc (keys : Keys) : Pr[= true | do
      let salt ← $ᵗ Bool
      let b ← $ᵗ Bool
      pure (decide (¬ (((keys b).1 ^^ salt) ≠ (keys false).1)))] = 1/2 := by
    simp only [probOutput_bind_eq_sum_fintype, Fintype.sum_bool]
    cases h₀ : (keys false).1 <;> cases h₁ : (keys true).1 <;> norm_num [h₀, h₁]
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
      repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ ENNReal.toReal_mul, ENNReal.toReal_inv]
  unfold rejectionProbability
  simp only [draws, adversary, bind_assoc, pure_bind, legal_iff]
  rw [probOutput_bind_of_const ($ᵗ Keys) (r := 1/2) (fun keys _ => hc keys)]
  norm_num

theorem toy_positive_with_collision (g) :
    advantage (fun _ => True) (adversary g) ≤ 1/4 := by
  have h := advantage_le (fun _ => True) (adversary g) 0 toy_hiding
  rw [toy_rejection] at h
  linarith

theorem toy_prefix_term_zero (g) : (terms (fun _ => True) (adversary g)).1 = 0 := by
  have h (keys : Keys) : ¬ PrefixRejected (fun _ => True) keys challenge := by
    simp [PrefixRejected, RecipientGame.runChecked_complete (prefix_run keys)]
  simp [terms, draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, h]

theorem collision_iff (keys : Keys) (salt b : Bool) :
    OutputCollision (fun _ => True) keys challenge salt b ↔
      ¬ Legal (fun _ => True) keys challenge salt b := by
  rw [legal_iff]
  unfold OutputCollision
  rw [RecipientGame.runChecked_complete (prefix_run keys)]
  cases b <;> simp [Challenge.deposit, challenge, priorState, DepositData.post,
    priorNote, NotePlan.resolve, St.empty, St.leaves, Note.cm, Prim, eq_comm]

theorem toy_other_term_zero (g) : (terms (fun _ => True) (adversary g)).2.2 = 0 := by
  have hn (keys : Keys) (salt b : Bool) :
      (¬ Legal (fun _ => True) keys challenge salt b ∧
       ¬ PrefixRejected (fun _ => True) keys challenge ∧
       ¬ OutputCollision (fun _ => True) keys challenge salt b) ↔ False := by
    rw [collision_iff]
    tauto
  simp [terms, draws, adversary, probEvent_bind_eq_tsum, Function.comp_def, hn]

theorem toy_collision_term (g) : (terms (fun _ => True) (adversary g)).2.1 = 1/2 := by
  have h := rejection_partition (fun _ => True) (adversary g)
  rw [toy_rejection, toy_prefix_term_zero, toy_other_term_zero] at h
  linarith

def cleanChallenge : OwnerGame.Challenge Prim Bool := { challenge with prior := [] }

def cleanAdversary (g : (Bool → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool) :
    OwnerGame.Adversary Prim Bool where
  State := Unit
  choose := fun _ => pure (cleanChallenge, ())
  guess := fun _ => g

theorem clean_legal (keys : Keys) (salt b : Bool) :
    Legal (fun _ => True) keys cleanChallenge salt b := by
  refine ⟨St.empty Prim (fun _ => True), rfl, ?_⟩
  norm_num [DepositData.guard, Challenge.deposit, cleanChallenge, challenge, St.empty,
    St.leaves, U128, maxU128]

theorem clean_rejection (g) : rejectionProbability (fun _ => True) (cleanAdversary g) = 0 := by
  simp [rejectionProbability, draws, cleanAdversary, clean_legal]

theorem toy_fresh_salt_zero (g) : advantage (fun _ => True) (cleanAdversary g) = 0 := by
  have h := advantage_le (fun _ => True) (cleanAdversary g) 0 toy_hiding
  rw [clean_rejection] at h
  exact le_antisymm (by linarith) (abs_nonneg _)

def guess (pk : Bool → Bool) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit cm] => !(cm == pk false)
  | _ => false

/-- Only the salt source changes: the attacker supplies false, to the same guarded game. -/
noncomputable def chosenSaltExperiment : ProbComp Bool := do
  let keys ← $ᵗ Keys
  let b ← $ᵗ Bool
  OwnerGame.challengeExp (fun _ => True) (cleanAdversary (fun pk log => pure (guess pk log)))
    keys cleanChallenge () false b

theorem chosen_salt_eq : chosenSaltExperiment = (do
    let keys ← $ᵗ Keys
    let b ← $ᵗ Bool
    pure (b == (b && !((keys true).1 == (keys false).1)))) := by
  unfold chosenSaltExperiment
  apply bind_congr
  intro keys
  apply bind_congr
  intro b
  simp only [OwnerGame.challengeExp, if_pos (clean_legal keys false b),
    legal_guarded_log _ keys cleanChallenge false b (clean_legal keys false b)]
  cases b <;> simp [cleanAdversary, guess, Challenge.history, Challenge.deposit,
    cleanChallenge, challenge, observerView, events, gameEvent, Tx.event, Note.cm, Prim]

theorem toy_chosen_salt_bias : |(Pr[= true | chosenSaltExperiment]).toReal - 1/2| = 1/4 := by
  rw [chosen_salt_eq]
  have hc : (Finset.univ.filter (fun keys : Keys => (keys true).1 ≠ (keys false).1)).card = 32 := by decide
  have ht : Fintype.card Keys = 64 := by decide
  have hp : Pr[fun keys : Keys => (keys true).1 ≠ (keys false).1 | $ᵗ Keys] = 1/2 := by
    rw [probEvent_uniformSample, hc, ht]
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
    norm_num
  have he : Pr[= true | do
      let keys ← $ᵗ Keys
      let b ← $ᵗ Bool
      pure (b == (b && !((keys true).1 == (keys false).1)))] = 3/4 := by
    rw [OracleComp.probOutput_congr (x := true) rfl
      (OracleComp.DeferredSampling.evalSPMF_bind_comm _ _ _)]
    rw [probOutput_bind_eq_sum_fintype]
    simp only [Fintype.sum_bool, probOutput_uniformSample, Fintype.card_bool]
    have hp' : Pr[= true | do
        let keys ← $ᵗ Keys
        pure (true == (true && !((keys true).1 == (keys false).1)))] = 1/2 := by
      simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def] using hp
    rw [hp']
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]
  rw [he]
  norm_num


theorem toy_chosen_salt_bound_false (g) :
    ¬ |(Pr[= true | chosenSaltExperiment]).toReal - 1/2| ≤
      (0 : ℝ)/2 + rejectionProbability (fun _ => True) (cleanAdversary g)/2 := by
  rw [toy_chosen_salt_bias, clean_rejection]
  norm_num

end LeanShieldedPool.OwnerGame.Toy
