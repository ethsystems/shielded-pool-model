import WithdrawGame.HonestToy
import WithdrawGame.LearnedKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.TransportControls
open GameCorrespondence Transport

/-- Removing the joint public-key-aware premise makes the zero-error conclusion false.
This reuses the public-key leak of `WithdrawGame.Toy`, with no rejection allowance. -/
theorem toy_drop_premise :
    ¬ advantage (fun _ => True) Toy.adversary ≤
      (0 : ℝ) + rejectionProbability (fun _ => True) Toy.adversary / 2 := by
  rw [Toy.toy_advantage, Toy.toy_rejection_probability_zero]
  norm_num

theorem toy_joint_premise_fails :
    ¬ MultiKeyPublicKeyPRF (P := Toy.Prim) (ι := Unit) 0 := by
  intro h
  exact toy_drop_premise (Transport.advantage_le (fun _ => True) Toy.adversary 0 h)

namespace Disclosure
open HonestToy

def cleanChallenge : Challenge Prim Unit :=
  { challenge with prior := [.deposit (note 0) (), .deposit (note 1) (), .deposit (note 2) ()] }

def cleanAdversary (g : (Unit → Bool) → List (PoolGame.Event (gamePrim Prim)) → ProbComp Bool) :
    Adversary Prim Unit where
  State := Unit
  choose := fun _ => pure (cleanChallenge, ())
  guess := fun _ => g

theorem clean_prefix (keys : Keys) :
    Run (fun _ => True) (cleanChallenge.prior.map (Intent.resolve keys)) (afterThird keys) :=
  Run.step (Run.step (Run.step Run.empty (Step.deposit (first_guard keys)))
    (Step.deposit (second_guard keys))) (Step.deposit (third_guard keys))

theorem clean_guard (keys : Keys) (b : Bool) :
    (cleanChallenge.withdrawal keys b).guard (afterThird keys) := by
  cases b <;>
    norm_num [WithdrawData.guard, Challenge.withdrawal, cleanChallenge, challenge, afterThird,
      afterSecond, afterFirst, DepositData.post, NotePlan.resolve,
      note, St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy,
      St.inTreeAt, St.leaves, St.fresh, WithdrawData.nf, Note.nf, Note.cm, Prim,
      U128, maxU128, bump]

theorem clean_legal (keys : Keys) : Legal (fun _ => True) keys cleanChallenge := by
  refine ⟨rfl, rfl, by change (1 : Fin 3) ≠ 2; decide, afterThird keys,
    RecipientGame.runChecked_complete (clean_prefix keys), ?_, ?_, clean_guard keys false,
    clean_guard keys true⟩ <;>
    simp [afterThird, afterSecond, afterFirst, DepositData.post, St.empty, cleanChallenge, challenge]

theorem clean_rejection_zero (g) :
    rejectionProbability (fun _ => True) (cleanAdversary g) = 0 := by
  simp [rejectionProbability, cleanAdversary, rejected_eq_not_legal, clean_legal]

/-- On this same primitive and schedule, every observer without the key has bias zero. -/
theorem toy_without_key_zero (g) : advantage (fun _ => True) (cleanAdversary g) = 0 := by
  have h := Transport.advantage_le (fun _ => True) (cleanAdversary g) 0 toy_multi_key_prf
  rw [clean_rejection_zero] at h
  exact le_antisymm (by linarith) (abs_nonneg _)

def leakedGuess (key : Prim.SpendKey) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .deposit _, .withdraw nf] => !(nf == key.2 1)
  | _ => false

/-- One interface mutation: after sampling the same keys, close the observer over keys ().
The challenger still calls the unchanged WithdrawGame challengeExp with its frozen guards. -/
noncomputable def leakedExperiment : ProbComp Bool := do
  let b ← $ᵗ Bool
  let keys ← $ᵗ Keys
  challengeExp (fun _ => True)
    (cleanAdversary (fun _ log => pure (leakedGuess (keys ()) log))) keys cleanChallenge () b

theorem leaked_guess_eq (keys : Keys) (b : Bool) :
    leakedGuess (keys ()) (observerView (cleanChallenge.history keys b)) =
      (b && !((keys ()).2 2 == (keys ()).2 1)) := by
  cases b <;> simp [leakedGuess, Challenge.history, Challenge.withdrawal, cleanChallenge, challenge,
    Intent.resolve, observerView, events, gameEvent, Tx.event, WithdrawData.nf,
    Note.nf, Note.cm, NotePlan.resolve, note, Prim]

theorem leaked_experiment_eq : leakedExperiment =
    (do let b ← $ᵗ Bool; let keys ← $ᵗ Keys;
        pure (b == (b && !((keys ()).2 2 == (keys ()).2 1)))) := by
  unfold leakedExperiment
  apply bind_congr
  intro b
  apply bind_congr
  intro keys
  simp only [challengeExp, if_pos (clean_legal keys),
    legal_guarded_log (fun _ => True) keys cleanChallenge (clean_legal keys) b,
    cleanAdversary, pure_bind, leaked_guess_eq]

theorem distinct_probability :
    Pr[fun keys : Keys => (keys ()).2 2 ≠ (keys ()).2 1 | $ᵗ Keys] = 3 / 4 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun keys : Keys => (keys ()).2 2 ≠ (keys ()).2 1)).card = 96 := by decide
  have ht : Fintype.card Keys = 128 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem toy_with_one_key_bias : |(Pr[= true | leakedExperiment]).toReal - 1 / 2| = 3 / 8 := by
  rw [leaked_experiment_eq, probOutput_bind_eq_sum_fintype]
  simp only [Fintype.sum_bool, probOutput_uniformSample, Fintype.card_bool]
  have hp : Pr[= true | do
      let keys ← $ᵗ Keys
      pure (true == (true && !((keys ()).2 2 == (keys ()).2 1)))] = 3 / 4 := by
    simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def] using
      distinct_probability
  rw [hp]
  norm_num
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

/-- The undeclared key disclosure invalidates the zero-error bound on the identical schedule. -/
theorem toy_disclosed_key_bound_false (g) :
    ¬ |(Pr[= true | leakedExperiment]).toReal - 1 / 2| ≤
      (0 : ℝ) + rejectionProbability (fun _ => True) (cleanAdversary g) / 2 := by
  rw [toy_with_one_key_bias, clean_rejection_zero]
  norm_num

end Disclosure
end LeanShieldedPool.WithdrawGame.TransportControls
