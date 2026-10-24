import WithdrawGame.DropPRF

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.LearnedKey
open GameCorrespondence

/-- A random two-entry function with a constant public key. -/
abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool → Bool
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool
  derivePub := fun _ => false
  commit := fun _ _ _ s => s
  nullify := fun cm k => k cm

abbrev Keys := Unit → Prim.SpendKey

def note (s : Bool) : NotePlan Prim Unit := ⟨(), 1, (), s⟩
def challenge : Challenge Prim Unit where
  prior := [.deposit (note false) (), .deposit (note true) ()]
  left := note false
  right := note true
  recipient := ()
  snapshot := 2

noncomputable def afterFirst (keys : Keys) : St Prim :=
  (DepositData.mk ((note false).resolve keys) ()).post (St.empty Prim (fun _ => True))
noncomputable def afterSecond (keys : Keys) : St Prim :=
  (DepositData.mk ((note true).resolve keys) ()).post (afterFirst keys)

theorem first_guard (keys : Keys) :
    (DepositData.mk ((note false).resolve keys) ()).guard (St.empty Prim (fun _ => True)) := by
  norm_num [DepositData.guard, NotePlan.resolve, note, St.empty, St.leaves, U128, maxU128]

theorem second_guard (keys : Keys) :
    (DepositData.mk ((note true).resolve keys) ()).guard (afterFirst keys) := by
  norm_num [DepositData.guard, afterFirst, DepositData.post, NotePlan.resolve, note,
    St.empty, St.leaves, Note.cm, Prim, U128, maxU128]
  decide

theorem prefix_run (keys : Keys) :
    Run (fun _ => True) (challenge.prior.map (Intent.resolve keys)) (afterSecond keys) :=
  Run.step (Run.step Run.empty (Step.deposit (first_guard keys))) (Step.deposit (second_guard keys))

theorem withdrawal_guard (keys : Keys) (b : Bool) :
    (challenge.withdrawal keys b).guard (afterSecond keys) := by
  cases b <;>
    norm_num [WithdrawData.guard, Challenge.withdrawal, challenge, afterSecond, afterFirst,
      DepositData.post, NotePlan.resolve, note, St.rootInWindow, St.pushWindow, rootWindow,
      St.empty, Note.ownedBy, St.inTreeAt, St.leaves, St.fresh, WithdrawData.nf,
      Note.nf, Note.cm, Prim, U128, maxU128, bump]

theorem legal (keys : Keys) : Legal (fun _ => True) keys challenge := by
  refine ⟨rfl, rfl, by change false ≠ true; decide, afterSecond keys, RecipientGame.runChecked_complete (prefix_run keys),
    ?_, ?_, withdrawal_guard keys false, withdrawal_guard keys true⟩ <;>
    simp [afterSecond, afterFirst, DepositData.post, St.empty, challenge]

theorem accepted (keys : Keys) (b : Bool) :
    Run (fun _ => True) (challenge.history keys b)
      ((challenge.withdrawal keys b).post (afterSecond keys)) :=
  Run.step (prefix_run keys) (Step.withdraw (withdrawal_guard keys b))

theorem guarded (keys : Keys) (b : Bool) :
    RecipientGame.guardedLog (fun _ => True) (challenge.history keys b) =
      some (observerView (challenge.history keys b)) := by
  simp [RecipientGame.guardedLog, RecipientGame.runChecked_complete (accepted keys b)]

/-- This is the control mutation: the observer gets one sampled spending key. -/
def leakedGuess (key : Prim.SpendKey) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .withdraw nf] => !(nf == key false)
  | _ => false

noncomputable def leakedExperiment : ProbComp Bool := by
  classical
  exact do
    let b ← $ᵗ Bool
    let keys ← $ᵗ Keys
    if Legal (fun _ => True) keys challenge then
      match RecipientGame.guardedLog (fun _ => True) (challenge.history keys b) with
      | none => $ᵗ Bool
      | some log => pure (b == leakedGuess (keys ()) log)
    else $ᵗ Bool

theorem leaked_guess_eq (keys : Keys) (b : Bool) :
    leakedGuess (keys ()) (observerView (challenge.history keys b)) =
      (b && !(keys () true == keys () false)) := by
  cases b <;> simp [leakedGuess, Challenge.history, Challenge.withdrawal, challenge,
    Intent.resolve, observerView, events, gameEvent, Tx.event, WithdrawData.nf,
    Note.nf, Note.cm, NotePlan.resolve, note, Prim]

theorem leaked_experiment_eq : leakedExperiment =
    (do let b ← $ᵗ Bool; let keys ← $ᵗ Keys;
        pure (b == (b && !(keys () true == keys () false)))) := by
  unfold leakedExperiment
  apply bind_congr
  intro b
  apply bind_congr
  intro keys
  simp only [if_pos (legal keys), guarded, leaked_guess_eq]

theorem toy_learned_key_advantage :
    |(Pr[= true | leakedExperiment]).toReal - 1 / 2| = 1 / 4 := by
  rw [leaked_experiment_eq, ← Toy.experiment_eq]
  exact Toy.toy_advantage

/-- Before disclosure this primitive meets the stronger public-key-aware premise with zero error. -/
theorem toy_public_key_prf : PublicKeyPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 := by
  intro test
  simp [Prim]

theorem toy_plain_prf : PlainPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 := by
  intro test
  simp [Prim]

noncomputable def assumptions : Assumptions Prim 2 1 where
  epsHiding := 0
  hiding_bound := by intros; simp [Prim]
  epsPRF := 0
  prf := toy_plain_prf
  commitmentSpread := RecipientGame.Rejection.spread_of_injective ⟨fun _ _ _ => Function.injective_id⟩
  nullifierSpread := ⟨by decide, by intro n k nf; simpa using
    (probEvent_le_one (mx := ($ᵗ Prim.Salt))
      (p := fun s => Prim.nullify (Prim.commit n.token n.amount n.ownerPubkey s) k = nf))⟩

theorem toy_disclosure_obstruction :
    assumptions.epsPRF = 0 ∧ assumptions.epsHiding = 0 ∧
    PublicKeyPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 ∧
    |(Pr[= true | leakedExperiment]).toReal - 1 / 2| = 1 / 4 :=
  ⟨rfl, rfl, toy_public_key_prf, toy_learned_key_advantage⟩

theorem toy_key_dependence :
    Prim.nullify false (fun _ => false) ≠ Prim.nullify false (fun _ => true) := by decide

/-- No key value can be read from the public-key interface in this control. -/
theorem public_key_constant (k : Prim.SpendKey) : Prim.derivePub k = false := rfl

end LeanShieldedPool.WithdrawGame.LearnedKey
