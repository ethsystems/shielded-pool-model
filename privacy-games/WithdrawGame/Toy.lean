import WithdrawGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.Toy
open GameCorrespondence

/-- A random two-entry function. The public key reveals only its false entry. -/
abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool → Bool
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool
  derivePub := fun k => k false
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

def guess (pk : Unit → Prim.PubKey) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .withdraw nf] => !(nf == pk ())
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
    guess (Prim.derivePub ∘ keys) (observerView (challenge.history keys b)) =
      (b && !(keys () true == keys () false)) := by
  cases b <;> simp [guess, Challenge.history, Challenge.withdrawal, challenge,
    Intent.resolve, observerView, events, gameEvent, Tx.event, WithdrawData.nf,
    Note.nf, Note.cm, NotePlan.resolve, note, Prim]

theorem experiment_eq : experiment (fun _ => True) adversary =
    (do let b ← $ᵗ Bool; let keys ← $ᵗ Keys;
        pure (b == (b && !(keys () true == keys () false)))) := by
  unfold experiment
  apply bind_congr
  intro b
  apply bind_congr
  intro keys
  simp only [adversary, pure_bind, challengeExp, if_pos (legal keys), guarded]
  rw [guess_eq]

theorem distinct_probability :
    Pr[fun keys : Keys => keys () true ≠ keys () false | $ᵗ Keys] = 1 / 2 := by
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun keys : Keys => keys () true ≠ keys () false)).card = 2 := by
    decide
  have htotal : Fintype.card Keys = 4 := by decide
  rw [hcard, htotal]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem toy_advantage : advantage (fun _ => True) adversary = 1 / 4 := by
  rw [advantage, experiment_eq]
  rw [probOutput_bind_eq_sum_fintype]
  simp only [Fintype.sum_bool, probOutput_uniformSample, Fintype.card_bool]
  have hp : Pr[= true | do
      let keys ← $ᵗ Keys
      pure (true == (true && !(keys () true == keys () false)))] = 1 / 2 := by
    simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def] using
      distinct_probability
  rw [hp]
  norm_num
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem toy_plain_prf : PlainPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 := by
  intro test
  simp [Prim]

theorem table_coordinate_probability (v : Bool) :
    Pr[fun f : Bool → Bool => f false = v | $ᵗ (Bool → Bool)] = 1 / 2 := by
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun f : Bool → Bool => f false = v)).card = 2 := by
    cases v <;> decide
  have htotal : Fintype.card (Bool → Bool) = 4 := by decide
  rw [hcard, htotal]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

/-- The public-key-aware test has distance 1/2, even though the plain PRF distance is zero. -/
theorem toy_public_key_prf_distance :
    |(Pr[= true | do
        let k ← $ᵗ Prim.SpendKey
        pure (Prim.nullify false k == Prim.derivePub k)]).toReal -
      (Pr[= true | do
        let k ← $ᵗ Prim.SpendKey
        let f ← $ᵗ (Prim.Commitment → Prim.Nullifier)
        pure (f false == Prim.derivePub k)]).toReal| = 1 / 2 := by
  have hr : Pr[= true | do
      let k ← $ᵗ Prim.SpendKey
      pure (Prim.nullify false k == Prim.derivePub k)] = 1 := by simp [Prim]
  have hi : Pr[= true | do
      let k ← $ᵗ Prim.SpendKey
      let f ← $ᵗ (Prim.Commitment → Prim.Nullifier)
      pure (f false == Prim.derivePub k)] = 1 / 2 := by
    rw [probOutput_bind_of_const ($ᵗ Prim.SpendKey) (r := 1 / 2)]
    · simp
    · intro k _
      simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def] using
        table_coordinate_probability (Prim.derivePub k)
  rw [hr, hi]
  norm_num [ENNReal.toReal_div]

theorem toy_public_key_prf_fails : ¬ PublicKeyPRF (P := Prim) ($ᵗ Prim.SpendKey) 0 := by
  intro h
  have htest := h (fun pk f => pure (f false == pk))
  rw [toy_public_key_prf_distance] at htest
  norm_num at htest

theorem toy_key_dependence :
    Prim.nullify false (fun _ => false) ≠ Prim.nullify false (fun _ => true) := by decide

/-- The full key cannot be recovered from the public key: two keys share the same public key. -/
theorem toy_no_public_key_recovery :
    ¬ ∃ recover : Prim.PubKey → Prim.SpendKey, ∀ k, recover (Prim.derivePub k) = k := by
  rintro ⟨recover, h⟩
  have h0 := congrFun (h (fun _ => false)) true
  have h1 := congrFun (h id) true
  simp at h0 h1
  exact Bool.noConfusion (h0.symm.trans h1)

noncomputable def assumptions : Assumptions Prim 2 1 where
  epsHiding := 0
  hiding_bound := by intros; simp [Prim]
  epsPRF := 0
  prf := toy_plain_prf
  commitmentSpread := RecipientGame.Rejection.spread_of_injective ⟨fun _ _ _ => Function.injective_id⟩
  nullifierSpread := ⟨by decide, by intro n k nf; simpa using
    (probEvent_le_one (mx := ($ᵗ Prim.Salt)) (p := fun s => Prim.nullify (Prim.commit n.token n.amount n.ownerPubkey s) k = nf))⟩

/-- No rejection or collision allowance is needed in this exact deterministic-salt schedule. -/
theorem toy_no_rejection (keys : Keys) (b : Bool) :
    RecipientGame.runChecked (St.empty Prim (fun _ => True)) (challenge.history keys b) ≠ none := by
  rw [RecipientGame.runChecked_complete (accepted keys b)]
  simp

theorem toy_rejection_probability_zero : rejectionProbability (fun _ => True) adversary = 0 := by
  have hr (keys : Keys) (b : Bool) : rejected (fun _ => True) keys challenge b = false := by
    simp [rejected, legal, RecipientGame.runChecked_complete (accepted keys b)]
  simp [rejectionProbability, adversary, hr]

/-- Perfect plain PRF security, perfect hiding, and both named spreads coexist with advantage 1/4.
This is a toy obstruction to using a PRF premise that omits the correlated public key. -/
theorem toy_obstruction :
    assumptions.epsPRF = 0 ∧ assumptions.epsHiding = 0 ∧
    advantage (fun _ => True) adversary = 1 / 4 ∧
    (∀ keys b, RecipientGame.runChecked (St.empty Prim (fun _ => True))
      (challenge.history keys b) ≠ none) :=
  ⟨rfl, rfl, toy_advantage, toy_no_rejection⟩

theorem toy_zero_error_bound_false (a b : ℝ) :
    ¬ advantage (fun _ => True) adversary ≤ a * assumptions.epsPRF + b * assumptions.epsHiding +
      rejectionProbability (fun _ => True) adversary / 2 := by
  rw [toy_advantage, toy_rejection_probability_zero]
  norm_num [assumptions]

end LeanShieldedPool.WithdrawGame.Toy
