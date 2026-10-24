import ChainGame.AdaptiveExample

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChosenWorldGame
open GameCorrespondence
variable {P : PrimSpec}

/-- Public metadata absent from the frozen event log. List order fixes nullifier positions. -/
inductive PublicData (P : PrimSpec) where
  | deposit (token : P.Token) (amount : Nat) (funding : P.Address)
  | transfer (snapshot : Nat)
  | withdraw (token : P.Token) (amount : Nat) (recipient : P.Address) (snapshot : Nat)

def publicData : Tx P → PublicData P
  | .deposit d => .deposit d.note.token d.note.amount d.funding
  | .transfer d => .transfer d.snapshot
  | .withdraw d => .withdraw d.note.token d.note.amount d.recipient d.snapshot

def PublicAgreement (left right : List (Tx P)) : Prop :=
  left.map publicData = right.map publicData

/-- Keep the frozen view and add the public call fields in matching transaction order. -/
abbrev Observation (P : PrimSpec) := List (PoolGame.Event (gamePrim P)) × List (PublicData P)

def observe (txs : List (Tx P)) : Observation P := (observerView txs, txs.map publicData)

noncomputable def guardedObserve (sup : P.Token → Prop) (txs : List (Tx P)) :
    Option (Observation P) :=
  (RecipientGame.runChecked (St.empty P sup) txs).map (fun _ => observe txs)

theorem guardedObserve_realizable {sup : P.Token → Prop} {txs : List (Tx P)}
    {log : Observation P} (h : guardedObserve sup txs = some log) :
    ∃ st, ∃ run : Run sup txs st,
      runObserverView run = log.1 ∧ txs.map publicData = log.2 := by
  obtain ⟨st, hs, hv⟩ := Option.map_eq_some_iff.mp h
  subst log
  exact ⟨st, by simpa using RecipientGame.runChecked_sound txs Run.empty hs, rfl, rfl⟩

noncomputable def publish (sup : P.Token → Prop) (world : ProbComp (List (Tx P))) :
    ProbComp (Option (Observation P)) := do
  let txs ← world
  return guardedObserve sup txs

theorem publish_realizable (sup : P.Token → Prop) (world : ProbComp (List (Tx P)))
    (log : Observation P) (h : some log ∈ support (publish sup world)) :
    ∃ txs ∈ support world, ∃ st, ∃ run : Run sup txs st,
      runObserverView run = log.1 ∧ txs.map publicData = log.2 := by
  simp [publish] at h
  obtain ⟨txs, ht, hl⟩ := h
  obtain ⟨st, run, hv⟩ := guardedObserve_realizable hl
  exact ⟨txs, ht, st, run, hv⟩

/-- The schedule fixes operation kind, position, amounts, addresses, tokens, and snapshots. -/
def Legal (left right : ProbComp (List (Tx P))) : Prop :=
  ∃ schedule, (∀ txs ∈ support left, txs.map publicData = schedule) ∧
    (∀ txs ∈ support right, txs.map publicData = schedule)

noncomputable def experiment (sup : P.Token → Prop)
    (left right : ProbComp (List (Tx P))) (guess : Observation P → Bool) : ProbComp Bool := by
  classical
  exact if Legal left right then do
    let b ← $ᵗ Bool
    let result ← publish sup (if b then right else left)
    match result with
    | none => $ᵗ Bool
    | some log => pure (b == guess log)
  else $ᵗ Bool

noncomputable def advantage (sup : P.Token → Prop)
    (left right : ProbComp (List (Tx P))) (guess : Observation P → Bool) : ℝ :=
  |(Pr[= true | experiment sup left right guess]).toReal - 1 / 2|

/-- A known spending key links an injective nullifier to its public output commitment. -/
theorem known_key_links {key : P.SpendKey} {c0 c1 : P.Commitment}
    (injective : Function.Injective (fun cm => P.nullify cm key)) (hne : c0 ≠ c1)
    (b : Bool) : (P.nullify (if b then c1 else c0) key = P.nullify c1 key) ↔ b = true := by
  cases b <;> simp [injective.eq_iff, hne]

namespace Counterexample
open RecipientGame.Rejection
abbrev Prim := Funded.Prim
abbrev Salt (k : Nat) := Fin (k + 8)

def note (k : Nat) (amount : Nat) (s : Salt k) : Note (Prim k) := ⟨(), amount, false, s⟩
def deposit (k : Nat) (s : Salt k) : DepositData (Prim k) := ⟨note k 2 s, ()⟩
def transfer (k : Nat) (s0 s1 s2 : Salt k) : TransferData (Prim k) where
  key := false
  in1 := note k 2 s0
  in2 := note k 0 1
  out1 := note k 1 s1
  out2 := note k 1 s2
  snapshot := 1

def withdraw (k : Nat) (b : Bool) (s1 s2 : Salt k) : WithdrawData (Prim k) where
  key := false
  note := note k 1 (if b then s2 else s1)
  recipient := ()
  snapshot := 3

def history (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) : List (Tx (Prim k)) :=
  [.deposit (deposit k s0), .transfer (transfer k s0 s1 s2), .withdraw (withdraw k b s1 s2)]

/-- All three commitment salts are independent challenger samples. -/
def sampleWorld (k : Nat) (b : Bool) : ProbComp (List (Tx (Prim k))) := do
  let s0 ← $ᵗ Salt k
  let s1 ← $ᵗ Salt k
  let s2 ← $ᵗ Salt k
  return history k b s0 s1 s2

theorem public_agreement (k : Nat) (s0 s1 s2 t0 t1 t2 : Salt k) :
    PublicAgreement (history k false s0 s1 s2) (history k true t0 t1 t2) := rfl

theorem legal (k : Nat) : Legal (sampleWorld k false) (sampleWorld k true) := by
  refine ⟨[.deposit () 2 (), .transfer 1, .withdraw () 1 () 3], ?_, ?_⟩ <;>
    intro txs h <;> simp [sampleWorld] at h <;>
    obtain ⟨s0, s1, s2, rfl⟩ := h <;> rfl

def guess (k : Nat) : Observation (Prim k) → Bool
  | ([.deposit _, .transfer _ _ _ c2, .withdraw nf], _) => nf == c2
  | _ => false

def Good (k : Nat) (s0 s1 s2 : Salt k) : Prop :=
  s0 ≠ 1 ∧ s1 ≠ s0 ∧ s1 ≠ 1 ∧ s2 ≠ s0 ∧ s2 ≠ s1 ∧ s2 ≠ 1

noncomputable def afterDeposit (k : Nat) (s0 : Salt k) : St (Prim k) :=
  (deposit k s0).post (St.empty (Prim k) (fun _ => True))
noncomputable def afterTransfer (k : Nat) (s0 s1 s2 : Salt k) : St (Prim k) :=
  (transfer k s0 s1 s2).post (afterDeposit k s0)
noncomputable def finalState (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) : St (Prim k) :=
  (withdraw k b s1 s2).post (afterTransfer k s0 s1 s2)

theorem deposit_guard (k : Nat) (s0 : Salt k) :
    (deposit k s0).guard (St.empty (Prim k) (fun _ => True)) := by
  norm_num [DepositData.guard, deposit, note, St.empty, St.leaves, U128, maxU128]

theorem transfer_guard (k : Nat) (s0 s1 s2 : Salt k) (h : Good k s0 s1 s2) :
    (transfer k s0 s1 s2).guard (afterDeposit k s0) := by
  rcases h with ⟨h0, h10, h11, h20, h21, h22⟩
  norm_num [TransferData.guard, transfer, afterDeposit, DepositData.post, deposit, note,
    St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy, Note.isBallast,
    St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2, Note.nf,
    Note.cm, U128, maxU128, Prim, Funded.Prim, h0, h10, h20, Ne.symm h21]

theorem withdraw_guard (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) (h : Good k s0 s1 s2) :
    (withdraw k b s1 s2).guard (afterTransfer k s0 s1 s2) := by
  rcases h with ⟨h0, h10, h11, h20, h21, h22⟩
  cases b <;>
    norm_num [WithdrawData.guard, withdraw, afterTransfer, afterDeposit, TransferData.post,
      transfer, DepositData.post, deposit, note, St.rootInWindow, St.pushWindow, rootWindow,
      St.empty, Note.ownedBy, St.inTreeAt, St.leaves, St.fresh, TransferData.nf1,
      TransferData.nf2, WithdrawData.nf, Note.nf, Note.cm, U128, maxU128, bump,
      Prim, Funded.Prim, h10, h11, h20, h22]

theorem accepted (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) (h : Good k s0 s1 s2) :
    Run (fun _ => True) (history k b s0 s1 s2) (finalState k b s0 s1 s2) := by
  exact Run.step (Run.step (Run.step Run.empty (Step.deposit (deposit_guard k s0)))
    (Step.transfer (transfer_guard k s0 s1 s2 h))) (Step.withdraw (withdraw_guard k b s0 s1 s2 h))

theorem distinguishes (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) (hne : s1 ≠ s2) :
    guess k (observe (history k b s0 s1 s2)) = b := by
  cases b <;> simp [guess, observe, observerView, events, gameEvent, Tx.event, history,
    deposit, transfer, withdraw, WithdrawData.nf, Note.nf, Note.cm, note, Prim, Funded.Prim, hne]

theorem checked_distinct (k : Nat) (b : Bool) (s0 s1 s2 : Salt k)
    (st : St (Prim k))
    (h : RecipientGame.runChecked (St.empty (Prim k) (fun _ => True)) (history k b s0 s1 s2) = some st) :
    s1 ≠ s2 := by
  have run : Run (fun _ => True) (history k b s0 s1 s2) st := by
    simpa using RecipientGame.runChecked_sound _ Run.empty h
  have he := run_events_guard run (gameEvent (Tx.event (.transfer (transfer k s0 s1 s2))))
    (by simp [history, observerView, events])
  exact he.2

abbrev Draw (k : Nat) := Bool × Salt k × Salt k × Salt k

def draws (k : Nat) : ProbComp (Draw k) := do
  let b ← $ᵗ Bool
  let s0 ← $ᵗ Salt k
  let s1 ← $ᵗ Salt k
  let s2 ← $ᵗ Salt k
  return (b, s0, s1, s2)

noncomputable def rejected (k : Nat) (a : Draw k) : Bool :=
  (RecipientGame.runChecked (St.empty (Prim k) (fun _ => True))
    (history k a.1 a.2.1 a.2.2.1 a.2.2.2)).isNone

theorem rejected_implies_bad (k : Nat) (a : Draw k) (h : rejected k a = true) :
    ¬ Good k a.2.1 a.2.2.1 a.2.2.2 := by
  intro hg
  have hr := RecipientGame.runChecked_complete (accepted k a.1 a.2.1 a.2.2.1 a.2.2.2 hg)
  simp [rejected, hr] at h

/-- Six exposures: one deposit/ballast, three commitment collisions, two output/ballast nullifiers. -/
theorem bad_probability_le (k : Nat) :
    Pr[fun a => ¬ Good k a.2.1 a.2.2.1 a.2.2.2 | draws k] ≤
      6 * ((k + 8 : Nat) : ℝ≥0∞)⁻¹ := by
  let r : ℝ≥0∞ := ((k + 8 : Nat) : ℝ≥0∞)⁻¹
  have hit (cs : List (Salt k)) : Pr[fun s => s ∈ cs | $ᵗ Salt k] ≤ cs.length * r := by
    exact hit_list_le (k + 8) (Funded.spread k) (note k 1 0) cs
  unfold draws
  apply probEvent_bind_le_of_forall_le
  intro b _
  refine le_trans (probEvent_bind_le_probEvent_add
    (p := fun s0 => s0 ∈ ([1] : List (Salt k))) (ε := 5 * r) ?_) ?_
  · intro s0 _ h0
    refine le_trans (probEvent_bind_le_probEvent_add
      (p := fun s1 => s1 ∈ [s0, 1]) (ε := 3 * r) ?_) ?_
    · intro s1 _ h1
      refine le_trans (probEvent_bind_le_probEvent_add
        (p := fun s2 => s2 ∈ [s0, s1, 1]) (ε := 0) ?_) ?_
      · intro s2 _ h2
        have hg : Good k s0 s1 s2 := by
          simpa [Good, List.mem_cons, List.mem_singleton, not_or, and_assoc] using
            And.intro h0 (And.intro h1 h2)
        simp [hg]
      · simpa using hit [s0, s1, 1]
    · calc
        _ ≤ 2 * r + 3 * r := add_le_add (by simpa using hit [s0, 1]) le_rfl
        _ = 5 * r := by ring
  · calc
      _ ≤ 1 * r + 5 * r := add_le_add (by simpa using hit [1]) le_rfl
      _ = 6 * r := by ring

theorem rejection_probability_le (k : Nat) :
    Pr[fun a => rejected k a = true | draws k] ≤ 6 * ((k + 8 : Nat) : ℝ≥0∞)⁻¹ :=
  (probEvent_mono (fun a _ h => rejected_implies_bad k a h)).trans (bad_probability_le k)

theorem rejection_real_le (k : Nat) :
    (Pr[= true | do let a ← draws k; pure (rejected k a)]).toReal ≤ 6 / (k + 8 : ℝ) := by
  have hf : (6 : ℝ≥0∞) * ((k + 8 : Nat) : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    finiteness
  have h := ENNReal.toReal_mono hf (rejection_probability_le k)
  simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp, Function.comp_def,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add, div_eq_mul_inv] using h

/-- Every accepted draw wins; rejected draws retain the frozen fair-bit convention. -/
theorem experiment_eq (k : Nat) :
    experiment (fun _ => True) (sampleWorld k false) (sampleWorld k true) (guess k) =
      (do let a ← draws k; if rejected k a then $ᵗ Bool else pure true) := by
  have hw (b : Bool) : (if b then sampleWorld k true else sampleWorld k false) = sampleWorld k b := by
    cases b <;> rfl
  rw [experiment, if_pos (legal k)]
  simp only [publish, bind_assoc, pure_bind]
  simp only [hw]
  simp only [sampleWorld, draws, bind_assoc, pure_bind]
  apply bind_congr
  intro b
  apply bind_congr
  intro s0
  apply bind_congr
  intro s1
  apply bind_congr
  intro s2
  cases hc : RecipientGame.runChecked (St.empty (Prim k) (fun _ => True)) (history k b s0 s1 s2) with
  | none => simp [guardedObserve, rejected, hc]
  | some st =>
    have hg := distinguishes k b s0 s1 s2 (checked_distinct k b s0 s1 s2 st hc)
    simp [guardedObserve, rejected, hc, hg]

theorem advantage_lower_bound (k : Nat) :
    1 / 2 - 3 / (k + 8 : ℝ) ≤
      advantage (fun _ => True) (sampleWorld k false) (sampleWorld k true) (guess k) := by
  have hd := RecipientGame.rejection_distance_le (draws k) (rejected k) (fun _ => pure true)
  rw [← experiment_eq] at hd
  simp [ProbComp.boolDistAdvantage] at hd
  have hr := rejection_real_le k
  simp only [bind_pure_comp] at hr
  have hh := le_abs_self ((Pr[= true | experiment (fun _ => True)
    (sampleWorld k false) (sampleWorld k true) (guess k)]).toReal - 1 / 2)
  unfold advantage
  have hd' := (abs_le.mp hd).1
  simp only [div_eq_mul_inv] at hr ⊢
  linarith

/-- Zero unproved premises. Hiding is perfect, but the guarded game has large advantage. -/
theorem concrete_counterexample :
    (Funded.assumptions 24).εHiding = 0 ∧
    (Pr[= true | do let a ← draws 24; pure (rejected 24 a)]).toReal ≤ 3 / 16 ∧
    13 / 32 ≤ advantage (fun _ => True) (sampleWorld 24 false) (sampleWorld 24 true) (guess 24) := by
  refine ⟨rfl, ?_, ?_⟩
  · convert rejection_real_le 24 using 1; norm_num
  · convert advantage_lower_bound 24 using 1; norm_num

/-- A hiding-plus-rejection-only extension is false for withdrawal-note privacy. -/
theorem transported_bound_false :
    ¬ advantage (fun _ => True) (sampleWorld 24 false) (sampleWorld 24 true) (guess 24) ≤
      3 * (Funded.assumptions 24).εHiding + (6 / (32 : ℝ)) / 2 := by
  have h := concrete_counterexample.2.2
  norm_num [Funded.assumptions]
  linarith

theorem concrete_good (k : Nat) : Good k 0 2 3 := by
  norm_num [Good, Fin.ext_iff]
  all_goals (simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)

theorem concrete_run (k : Nat) (b : Bool) :
    Run (fun _ => True) (history k b 0 2 3) (finalState k b 0 2 3) :=
  accepted k b 0 2 3 (concrete_good k)

theorem concrete_in_support (k : Nat) (b : Bool) :
    history k b 0 2 3 ∈ support (sampleWorld k b) := by
  simp only [sampleWorld, mem_support_bind_iff, mem_support_uniformSample,
    true_and, support_pure, Set.mem_singleton_iff]
  exact ⟨0, 2, 3, rfl⟩

theorem concrete_published (k : Nat) (b : Bool) :
    some (observe (history k b 0 2 3)) ∈ support (publish (fun _ => True) (sampleWorld k b)) := by
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  refine ⟨_, concrete_in_support k b, ?_⟩
  simp [guardedObserve, RecipientGame.runChecked_complete (concrete_run k b)]

theorem withdraws_exact_output (k : Nat) (b : Bool) (s0 s1 s2 : Salt k) :
    (withdraw k b s1 s2).note =
      (if b then (transfer k s0 s1 s2).out2 else (transfer k s0 s1 s2).out1) := by
  cases b <;> rfl

theorem only_withdrawal_differs (k : Nat) (s0 s1 s2 : Salt k) :
    (history k false s0 s1 s2).take 2 = (history k true s0 s1 s2).take 2 ∧
    (withdraw k false s1 s2).key = (withdraw k true s1 s2).key ∧
    (withdraw k false s1 s2).snapshot = (withdraw k true s1 s2).snapshot := by
  exact ⟨rfl, rfl, rfl⟩

theorem different_notes (k : Nat) :
    (withdraw k false 2 3).note ≠ (withdraw k true 2 3).note := by
  intro h
  have hs := congrArg Note.salt h
  have hn := (concrete_good k).2.2.2.2.1
  exact hn hs.symm

theorem actual_rejection_transport_false (coefficient : ℝ) :
    ¬ advantage (fun _ => True) (sampleWorld 24 false) (sampleWorld 24 true) (guess 24) ≤
      coefficient * (Funded.assumptions 24).εHiding +
        (Pr[= true | do let a ← draws 24; pure (rejected 24 a)]).toReal / 2 := by
  have hr := concrete_counterexample.2.1
  have ha := concrete_counterexample.2.2
  simp only [Funded.assumptions, mul_zero, zero_add]
  linarith

end Counterexample
end LeanShieldedPool.ChosenWorldGame
