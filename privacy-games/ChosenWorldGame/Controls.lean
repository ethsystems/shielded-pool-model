import ChosenWorldGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChosenWorldGame.Controls
open GameCorrespondence

abbrev Prim : PrimSpec := { RecipientGame.Rejection.Funded.Prim 0 with Address := Bool }

def deposit (amount : Nat) (funding : Bool) : DepositData Prim :=
  ⟨⟨(), amount, false, 0⟩, funding⟩
def world (amount : Nat) (funding : Bool) : List (Tx Prim) := [.deposit (deposit amount funding)]

/-- Mutation 1 removes only amount agreement. -/
def eraseAmount : PublicData Prim → PublicData Prim
  | .deposit t _ f => .deposit t 0 f
  | .withdraw t _ r s => .withdraw t 0 r s
  | x => x

/-- Mutation 2 removes only funding-address agreement. -/
def eraseFunding : PublicData Prim → PublicData Prim
  | .deposit t a _ => .deposit t a false
  | x => x

def MutatedAgreement (erase : PublicData Prim → PublicData Prim) (left right : List (Tx Prim)) : Prop :=
  left.map (erase ∘ publicData) = right.map (erase ∘ publicData)

def amountGuess : Observation Prim → Bool
  | (_, [.deposit _ amount _]) => amount == 2
  | _ => false

def fundingGuess : Observation Prim → Bool
  | (_, [.deposit _ _ funding]) => funding
  | _ => false

theorem run (amount : Nat) (funding : Bool) (hn : amount ≠ 0) (hu : U128 amount) :
    Run (fun _ => True) (world amount funding)
      ((deposit amount funding).post (St.empty Prim (fun _ => True))) := by
  apply Run.step Run.empty
  apply Step.deposit
  simpa [DepositData.guard, deposit, St.empty, St.leaves] using And.intro hn hu

theorem guarded (amount : Nat) (funding : Bool) (hn : amount ≠ 0) (hu : U128 amount) :
    guardedObserve (fun _ => True) (world amount funding) = some (observe (world amount funding)) := by
  simp [guardedObserve, RecipientGame.runChecked_complete (run amount funding hn hu)]

theorem amount_mutation :
    MutatedAgreement eraseAmount (world 1 false) (world 2 false) ∧
    ¬ PublicAgreement (world 1 false) (world 2 false) ∧
    observerView (world 1 false) = observerView (world 2 false) ∧
    amountGuess (observe (world 1 false)) = false ∧
    amountGuess (observe (world 2 false)) = true := by
  simp [MutatedAgreement, PublicAgreement, world, publicData, deposit, eraseAmount,
    Function.comp_def, observerView, events, gameEvent, Tx.event, Note.cm, Prim,
    RecipientGame.Rejection.Funded.Prim, amountGuess, observe]

theorem funding_mutation :
    MutatedAgreement eraseFunding (world 1 false) (world 1 true) ∧
    ¬ PublicAgreement (world 1 false) (world 1 true) ∧
    observerView (world 1 false) = observerView (world 1 true) ∧
    fundingGuess (observe (world 1 false)) = false ∧
    fundingGuess (observe (world 1 true)) = true := by
  simp [MutatedAgreement, PublicAgreement, world, publicData, deposit, eraseFunding,
    Function.comp_def, observerView, events, gameEvent, Tx.event, Note.cm, Prim,
    RecipientGame.Rejection.Funded.Prim, fundingGuess, observe]

noncomputable def mutatedExperiment (erase : PublicData Prim → PublicData Prim)
    (left right : List (Tx Prim)) (guess : Observation Prim → Bool) : ProbComp Bool := by
  classical
  exact if MutatedAgreement erase left right then do
    let b ← $ᵗ Bool
    match guardedObserve (fun _ => True) (if b then right else left) with
    | none => $ᵗ Bool
    | some log => pure (b == guess log)
  else $ᵗ Bool

theorem amount_attack :
    mutatedExperiment eraseAmount (world 1 false) (world 2 false) amountGuess = (do let _ ← $ᵗ Bool; pure true) := by
  rw [mutatedExperiment, if_pos amount_mutation.1]
  have h1 := guarded 1 false (by decide) (by norm_num [U128, maxU128])
  have h2 := guarded 2 false (by decide) (by norm_num [U128, maxU128])
  have he (b : Bool) :
      (match guardedObserve (fun _ => True) (if b then world 2 false else world 1 false) with
       | none => $ᵗ Bool
       | some log => pure (b == amountGuess log)) = (pure true : ProbComp Bool) := by
    cases b <;> simp [h1, h2, amount_mutation.2.2.2.1, amount_mutation.2.2.2.2]
  simp only [he]

theorem funding_attack :
    mutatedExperiment eraseFunding (world 1 false) (world 1 true) fundingGuess = (do let _ ← $ᵗ Bool; pure true) := by
  rw [mutatedExperiment, if_pos funding_mutation.1]
  have h1 := guarded 1 false (by decide) (by norm_num [U128, maxU128])
  have h2 := guarded 1 true (by decide) (by norm_num [U128, maxU128])
  have he (b : Bool) :
      (match guardedObserve (fun _ => True) (if b then world 1 true else world 1 false) with
       | none => $ᵗ Bool
       | some log => pure (b == fundingGuess log)) = (pure true : ProbComp Bool) := by
    cases b <;> simp [h1, h2, funding_mutation.2.2.2.1, funding_mutation.2.2.2.2]
  simp only [he]

theorem amount_advantage :
    |(Pr[= true | mutatedExperiment eraseAmount (world 1 false) (world 2 false) amountGuess]).toReal -
      (1 / 2 : ℝ)| = 1 / 2 := by
  rw [amount_attack]
  norm_num

theorem funding_advantage :
    |(Pr[= true | mutatedExperiment eraseFunding (world 1 false) (world 1 true) fundingGuess]).toReal -
      (1 / 2 : ℝ)| = 1 / 2 := by
  rw [funding_attack]
  norm_num

end LeanShieldedPool.ChosenWorldGame.Controls
