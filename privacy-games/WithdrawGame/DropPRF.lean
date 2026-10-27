import WithdrawGame.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.DropPRF
open GameCorrespondence

/-- Key-dependent nullifiers reveal their input commitment. Public keys are constant. -/
abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool → Bool
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool × Bool
  derivePub := fun _ => false
  commit := fun _ _ _ s => s
  nullify := fun cm k => (cm, k false)

abbrev Keys := Unit → Prim.SpendKey

def note (s : Bool) : NotePlan Prim Unit := ⟨(), 1, (), s⟩
def challenge : Challenge Prim Unit where
  prior := [.deposit (note false) (), .deposit (note true) ()]
  left := note false
  right := note true
  recipient := ()
  snapshot := 2

def guess (_pk : Unit → Prim.PubKey) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .withdraw nf] => nf.1
  | _ => false

def adversary : Adversary Prim Unit where
  State := Unit
  choose := fun _ => pure (challenge, ())
  guess := fun _ pk log => pure (guess pk log)

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

theorem guess_eq (keys : Keys) (b : Bool) :
    guess (Prim.derivePub ∘ keys) (observerView (challenge.history keys b)) = b := by
  cases b <;> rfl

theorem experiment_eq : experiment (fun _ => True) adversary =
    (do let b ← $ᵗ Bool; let _keys ← $ᵗ Keys; pure (b == b)) := by
  unfold experiment
  apply bind_congr
  intro b
  apply bind_congr
  intro keys
  simp only [adversary, pure_bind, challengeExp, if_pos (legal keys), guarded]
  rw [guess_eq]

theorem toy_drop_prf_advantage : advantage (fun _ => True) adversary = 1 / 2 := by
  rw [advantage, experiment_eq]
  norm_num

theorem toy_key_dependence :
    Prim.nullify false (fun _ => false) ≠ Prim.nullify false (fun _ => true) := by decide

theorem commitment_spread : RecipientGame.Rejection.CommitmentSpread (P := Prim) 2 :=
  RecipientGame.Rejection.spread_of_injective ⟨fun _ _ _ => Function.injective_id⟩

theorem nullifier_spread : ChainGame.NullifierSpread (P := Prim) 2 := by
  apply ChainGame.nullifierSpread_of_injective 2 commitment_spread
  intro k x y h
  exact congrArg Prod.fst h

theorem hiding_zero (t a pk t' a' pk') (test : Prim.Commitment → ProbComp Bool) :
    |(Pr[= true | do let s ← $ᵗ Prim.Salt; test (Prim.commit t a pk s)]).toReal -
      (Pr[= true | do let s ← $ᵗ Prim.Salt; test (Prim.commit t' a' pk' s)]).toReal| = 0 := by
  simp [Prim]

theorem random_table_probability :
    Pr[fun f : Bool → Bool × Bool => (f false).1 = false | $ᵗ (Bool → Bool × Bool)] = 1 / 2 := by
  rw [probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun f : Bool → Bool × Bool => (f false).1 = false)).card = 8 := by decide
  have ht : Fintype.card (Bool → Bool × Bool) = 16 := by decide
  rw [hc, ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem toy_plain_prf_fails : ¬ PlainPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 := by
  intro h
  have ht := h (fun f => pure ((f false).1 == false))
  have hr : Pr[= true | do
      let k ← $ᵗ Prim.SpendKey
      pure ((Prim.nullify false k).1 == false)] = 1 := by simp [Prim]
  have hi : Pr[= true | do
      let f ← $ᵗ (Prim.Commitment → Prim.Nullifier)
      pure ((f false).1 == false)] = 1 / 2 := by
    simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def] using
      random_table_probability
  rw [hr, hi] at ht
  norm_num [ENNReal.toReal_div] at ht

end LeanShieldedPool.WithdrawGame.DropPRF
