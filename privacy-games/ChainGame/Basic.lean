import RecipientGame.Rejection

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame
open GameCorrespondence RecipientGame
variable {P : PrimSpec}

abbrev OutputRef := Nat × Bool

structure Template (P : PrimSpec) where
  body : TransferData P
  input1 : Option OutputRef := none
  input2 : Option OutputRef := none

def output (d : TransferData P) (slot : Bool) : Note P := if slot then d.out2 else d.out1

def resolveNote (history : List (TransferData P)) (ref : Option OutputRef)
    (fallback : Note P) : Note P :=
  match ref with
  | none => fallback
  | some (i, slot) => ((history[i]?).map (fun d => output d slot)).getD fallback

def resolve (history : List (TransferData P)) (t : Template P) : TransferData P :=
  { t.body with
    in1 := resolveNote history t.input1 t.body.in1
    in2 := resolveNote history t.input2 t.body.in2 }

def Backward (index : Nat) (ref : Option OutputRef) : Prop :=
  ∀ r ∈ ref, r.1 < index

def Scoped (start : Nat) : List (Template P) → Prop
  | [] => True
  | t :: ts => Backward start t.input1 ∧ Backward start t.input2 ∧ Scoped (start + 1) ts

def RecipientOnly (t u : Template P) : Prop :=
  t.input1 = u.input1 ∧ t.input2 = u.input2 ∧ t.body.snapshot = u.body.snapshot ∧
  PoolGame.RecipientOnly (transferWitness t.body) (transferWitness u.body)

def RecipientPair (ts us : List (Template P)) : Prop :=
  Scoped 0 ts ∧ Scoped 0 us ∧ List.Forall₂ RecipientOnly ts us

def sampleWorld [SampleableType P.Salt] (history : List (TransferData P)) :
    List (Template P) → ProbComp (List (TransferData P))
  | [] => pure []
  | t :: ts => do
    let s1 ← $ᵗ P.Salt
    let s2 ← $ᵗ P.Salt
    let d := withSalts (resolve history t) s1 s2
    let rest ← sampleWorld (history ++ [d]) ts
    return d :: rest

inductive Resolves : List (TransferData P) → List (Template P) → List (TransferData P) → Prop
  | nil (history : List (TransferData P)) : Resolves history [] []
  | cons (history : List (TransferData P)) (t : Template P) (ts : List (Template P))
      (s1 s2 : P.Salt) (rest : List (TransferData P))
      (tail : Resolves (history ++ [withSalts (resolve history t) s1 s2]) ts rest) :
      Resolves history (t :: ts) (withSalts (resolve history t) s1 s2 :: rest)

theorem sampleWorld_resolves [SampleableType P.Salt] (history : List (TransferData P))
    (ts : List (Template P)) (ds : List (TransferData P))
    (h : ds ∈ support (sampleWorld history ts)) : Resolves history ts ds := by
  induction ts generalizing history ds with
  | nil => simp [sampleWorld] at h; subst ds; exact .nil _
  | cons t ts ih =>
    simp [sampleWorld] at h
    obtain ⟨s1, s2, rest, hr, rfl⟩ := h
    exact .cons history t ts s1 s2 rest (ih _ _ hr)

theorem resolves_length {history : List (TransferData P)} {ts : List (Template P)}
    {ds : List (TransferData P)} (h : Resolves history ts ds) : ds.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa using congrArg Nat.succ ih

def HistoryMinted (st : St P) (history : List (TransferData P)) : Prop :=
  ∀ d ∈ history, d.out1 ∈ st.minted ∧ d.out2 ∈ st.minted

theorem historyMinted_step (st : St P) (history : List (TransferData P))
    (d : TransferData P) (h : HistoryMinted st history) :
    HistoryMinted (d.post st) (history ++ [d]) := by
  intro e he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact ⟨List.mem_append_left _ (h e he).1, List.mem_append_left _ (h e he).2⟩
  · simp [TransferData.post]

theorem referenced_note_minted (st : St P) (history : List (TransferData P))
    (i : Nat) (slot : Bool) (fallback : Note P) (h : HistoryMinted st history)
    (hi : i < history.length) :
    resolveNote history (some (i, slot)) fallback ∈ st.minted := by
  have hm := h history[i] (List.getElem_mem hi)
  simp only [resolveNote, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  cases slot <;> simp [output, hm.1, hm.2]

noncomputable def publish [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (ts : List (Template P)) :
    ProbComp (Option (List (PoolGame.Event (gamePrim P)))) := do
  let ds ← sampleWorld [] ts
  return guardedLog sup (setup ++ ds.map Tx.transfer)

theorem publish_realizable [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (ts : List (Template P))
    (log : List (PoolGame.Event (gamePrim P))) (h : some log ∈ support (publish sup setup ts)) :
    ∃ ds ∈ support (sampleWorld [] ts), ∃ st,
      ∃ run : Run sup (setup ++ ds.map Tx.transfer) st, runObserverView run = log := by
  simp [publish] at h
  obtain ⟨ds, hs, hl⟩ := h
  obtain ⟨st, run, hv⟩ := guardedLog_realizable hl
  exact ⟨ds, hs, st, run, hv⟩

theorem publish_resolves [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (ts : List (Template P))
    (log : List (PoolGame.Event (gamePrim P))) (h : some log ∈ support (publish sup setup ts)) :
    ∃ ds, Resolves [] ts ds ∧ ∃ st,
      ∃ run : Run sup (setup ++ ds.map Tx.transfer) st, runObserverView run = log := by
  obtain ⟨ds, hs, st, run, hv⟩ := publish_realizable sup setup ts log h
  exact ⟨ds, sampleWorld_resolves [] ts ds hs, st, run, hv⟩

theorem resolveNote_reference (history : List (TransferData P)) (i : Nat) (slot : Bool)
    (fallback : Note P) (d : TransferData P) (h : history[i]? = some d) :
    resolveNote history (some (i, slot)) fallback = output d slot := by
  simp [resolveNote, h]

theorem backward_reference_exists (history : List (TransferData P)) (i : Nat) (slot : Bool)
    (h : Backward history.length (some (i, slot))) :
    ∃ d, history[i]? = some d := by
  have hi : i < history.length := h (i, slot) rfl
  exact ⟨history[i], List.getElem?_eq_getElem hi⟩

theorem resolve_reference_owned (history : List (TransferData P)) (i : Nat) (slot : Bool)
    (fallback : Note P) (key : P.SpendKey) (d : TransferData P)
    (h : history[i]? = some d) (owned : (output d slot).ownedBy key) :
    (resolveNote history (some (i, slot)) fallback).ownedBy key := by
  rw [resolveNote_reference history i slot fallback d h]
  exact owned

structure Adversary (P : PrimSpec) where
  State : Type
  chooseWorlds : ProbComp (List (Template P) × List (Template P) × State)
  distinguish : State → OracleComp (PoolGame.observerSpec (gamePrim P)) Bool

abbrev Draw (adv : Adversary P) := Option (adv.State × Bool × List (Tx P))

noncomputable def draws [SampleableType P.Salt] (setup : List (Tx P))
    (adv : Adversary P) : ProbComp (Draw adv) := by
  classical
  exact do
    let (ts, us, state) ← adv.chooseWorlds
    if RecipientPair ts us then do
      let b ← $ᵗ Bool
      let ds ← sampleWorld [] (if b then us else ts)
      return some (state, b, setup ++ ds.map Tx.transfer)
    else pure none

def idealResponse (adv : Adversary P) : Draw adv → ProbComp Bool
  | none => $ᵗ Bool
  | some (state, b, txs) => do
      let g ← simulateQ (PoolGame.observerImpl (observerView txs)) (adv.distinguish state)
      return b == g

noncomputable def rejected (sup : P.Token → Prop) {adv : Adversary P} : Draw adv → Bool
  | none => false
  | some (_, _, txs) => (runChecked (St.empty P sup) txs).isNone

theorem accepted_draw_realizable (sup : P.Token → Prop) (adv : Adversary P)
    (state : adv.State) (b : Bool) (txs : List (Tx P))
    (h : rejected sup (some (state, b, txs) : Draw adv) = false) :
    ∃ st, ∃ run : Run sup txs st, runObserverView run = observerView txs := by
  unfold rejected at h
  cases hr : runChecked (St.empty P sup) txs with
  | none => simp [hr] at h
  | some st =>
    exact ⟨st, by simpa using runChecked_sound txs Run.empty hr, rfl⟩

noncomputable def experiment [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : Adversary P) : ProbComp Bool := do
  let draw ← draws setup adv
  if rejected sup draw then $ᵗ Bool else idealResponse adv draw

noncomputable def advantage [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : Adversary P) : ℝ :=
  |(Pr[= true | experiment sup setup adv]).toReal - 1 / 2|

noncomputable def idealAdvantage [SampleableType P.Salt]
    (setup : List (Tx P)) (adv : Adversary P) : ℝ :=
  |(Pr[= true | draws setup adv >>= idealResponse adv]).toReal - 1 / 2|

noncomputable def rejectionProbability [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : Adversary P) : ℝ :=
  (Pr[= true | do let draw ← draws setup adv; pure (rejected sup draw)]).toReal

theorem advantage_le_ideal_add_rejection [SampleableType P.Salt]
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) :
    advantage sup setup adv ≤ idealAdvantage setup adv + rejectionProbability sup setup adv / 2 := by
  have hd := rejection_distance_le (draws setup adv) (rejected sup) (idealResponse adv)
  have ht := abs_sub_le (Pr[= true | experiment sup setup adv]).toReal
    (Pr[= true | draws setup adv >>= idealResponse adv]).toReal (1 / 2)
  unfold advantage idealAdvantage rejectionProbability
  unfold experiment at ht ⊢
  unfold ProbComp.boolDistAdvantage at hd
  linarith

theorem illegal_experiment_fair [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : Adversary P) (ts us : List (Template P)) (state : adv.State)
    (hc : adv.chooseWorlds = pure (ts, us, state)) (hp : ¬ RecipientPair ts us) :
    experiment sup setup adv = $ᵗ Bool := by
  simp [experiment, draws, hc, hp, rejected, idealResponse]

abbrev CommitmentHistory (P : PrimSpec) := List (P.Commitment × P.Commitment)

def commitmentHistory (history : List (TransferData P)) : CommitmentHistory P :=
  history.map (fun d => (d.out1.cm, d.out2.cm))

def referenceNf (history : CommitmentHistory P) (ref : Option OutputRef)
    (key : P.SpendKey) (fallback : P.Nullifier) : P.Nullifier :=
  match ref with
  | none => fallback
  | some (i, slot) => ((history[i]?).map (fun cs => P.nullify
      (if slot then cs.2 else cs.1) key)).getD fallback

def rewriteLog : List (Template P) → CommitmentHistory P →
    List (PoolGame.Event (gamePrim P)) → List (PoolGame.Event (gamePrim P))
  | t :: ts, history, .transfer n1 n2 c1 c2 :: log =>
      .transfer (referenceNf history t.input1 t.body.key n1)
        (referenceNf history t.input2 t.body.key n2) c1 c2 ::
        rewriteLog ts (history ++ [(c1, c2)]) log
  | _, _, log => log

theorem resolveNote_nf (history : List (TransferData P)) (ref : Option OutputRef)
    (fallback : Note P) (key : P.SpendKey) :
    (resolveNote history ref fallback).nf key =
      referenceNf (commitmentHistory history) ref key (fallback.nf key) := by
  cases ref with
  | none => rfl
  | some r =>
    rcases r with ⟨i, slot⟩
    simp only [resolveNote, referenceNf, commitmentHistory, List.getElem?_map]
    cases h : history[i]? with
    | none => rfl
    | some d => cases slot <;> rfl

theorem sampleWorld_observer_bind [SampleableType P.Salt] {α : Type}
    (ts : List (Template P)) (history : List (TransferData P))
    (f : List (PoolGame.Event (gamePrim P)) → ProbComp α) :
    (do let ds ← sampleWorld history ts; f (observerView (ds.map Tx.transfer))) =
      (do let log ← PoolGame.publish (ts.map (fun t => transferWitness t.body))
          f (rewriteLog ts (commitmentHistory history) log)) := by
  induction ts generalizing history f with
  | nil => simp [sampleWorld, PoolGame.publish, observerView, events, rewriteLog]
  | cons t ts ih =>
    simp only [sampleWorld, List.map_cons, PoolGame.publish, bind_assoc]
    apply bind_congr
    intro s1
    apply bind_congr
    intro s2
    simp only [pure_bind]
    let d := withSalts (resolve history t) s1 s2
    have he : gameEvent (Tx.event (.transfer d)) =
        PoolGame.Event.transfer
          (referenceNf (commitmentHistory history) t.input1 t.body.key t.body.nf1)
          (referenceNf (commitmentHistory history) t.input2 t.body.key t.body.nf2)
          d.out1.cm d.out2.cm := by
      simp only [gameEvent, Tx.event, TransferData.nf1, TransferData.nf2,
        d, withSalts, resolve, resolveNote_nf]
    change (do let rest ← sampleWorld (history ++ [d]) ts
               f (gameEvent (Tx.event (.transfer d)) :: observerView (rest.map Tx.transfer))) = _
    rw [ih (history ++ [d]) (fun log => f (gameEvent (Tx.event (.transfer d)) :: log))]
    apply bind_congr
    intro log
    rw [he]
    simp only [rewriteLog, PoolGame.TransferWitness.toEvent, transferWitness,
      commitmentHistory, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem rewriteLog_congr (ts us : List (Template P))
    (h : List.Forall₂ RecipientOnly ts us) (history : CommitmentHistory P)
    (log : List (PoolGame.Event (gamePrim P))) :
    rewriteLog ts history log = rewriteLog us history log := by
  induction h generalizing history log with
  | nil => rfl
  | @cons t u ts us htu hrest ih =>
    rcases htu with ⟨h1, h2, _, hb⟩
    have hk : t.body.key = u.body.key := hb.2.2.1
    cases log with
    | nil => rfl
    | cons e log =>
      cases e <;> simp only [rewriteLog]
      rw [h1, h2, hk, ih]

theorem project_legal (ts us : List (Template P)) (h : List.Forall₂ RecipientOnly ts us) :
    PoolGame.LegalChallenge (ts.map (fun t => transferWitness t.body))
      (us.map (fun t => transferWitness t.body)) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.2.2.2 ih

def rewriteObserver (setup : List (Tx P)) (ts : List (Template P)) :
    QueryImpl (PoolGame.observerSpec (gamePrim P))
      (OracleComp (PoolGame.observerSpec (gamePrim P))) :=
  fun _ => do
    let log ← query (spec := PoolGame.observerSpec (gamePrim P)) ()
    return observerView setup ++ rewriteLog ts [] log

theorem rewriteObserver_simulate (setup : List (Tx P)) (ts : List (Template P))
    (log : List (PoolGame.Event (gamePrim P)))
    (oa : OracleComp (PoolGame.observerSpec (gamePrim P)) Bool) :
    simulateQ (PoolGame.observerImpl log) (simulateQ (rewriteObserver setup ts) oa) =
      simulateQ (PoolGame.observerImpl (observerView setup ++ rewriteLog ts [] log)) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

noncomputable def projectAdversary (setup : List (Tx P)) (adv : Adversary P) :
    PoolGame.TransferIndAdv (gamePrim P) := by
  classical
  exact {
    State := Option (adv.State × List (Template P))
    chooseWorlds := do
      let (ts, us, state) ← adv.chooseWorlds
      if RecipientPair ts us then
        pure (ts.map (fun t => transferWitness t.body),
          us.map (fun t => transferWitness t.body), some (state, ts))
      else pure ([], [], none)
    distinguish := fun state => match state with
      | none => pure true
      | some (state, ts) => simulateQ (rewriteObserver setup ts) (adv.distinguish state) }

theorem ideal_eq_v1 [SampleableType P.Salt] (setup : List (Tx P)) (adv : Adversary P) :
    (draws setup adv >>= idealResponse adv) =
      PoolGame.transferIndExp (projectAdversary setup adv) := by
  classical
  simp only [draws, PoolGame.transferIndExp, projectAdversary, bind_assoc]
  apply bind_congr
  intro a
  rcases a with ⟨ts, us, state⟩
  by_cases hp : RecipientPair ts us
  · simp only [hp, if_pos, pure_bind, PoolGame.transferChallengeExp,
      project_legal ts us hp.2.2, bind_assoc]
    apply bind_congr
    intro b
    simp only [idealResponse, observerView_append, rewriteObserver_simulate]
    cases b with
    | false =>
      simpa [commitmentHistory] using sampleWorld_observer_bind ts []
        (fun log => do
          let g ← simulateQ (PoolGame.observerImpl (observerView setup ++ log))
            (adv.distinguish state)
          return (false == g))
    | true =>
      have hr (log : List (PoolGame.Event (gamePrim P))) := rewriteLog_congr ts us hp.2.2 [] log
      simpa only [Bool.true_eq, if_true, commitmentHistory, List.map_nil, hr] using
        sampleWorld_observer_bind us []
          (fun log => do
            let g ← simulateQ (PoolGame.observerImpl (observerView setup ++ log))
              (adv.distinguish state)
            return (true == g))
  · simp [hp, idealResponse, PoolGame.transferChallengeExp, PoolGame.LegalChallenge,
      PoolGame.publish]

structure BoundAssumptions [SampleableType P.Salt] [DecidableEq P.Commitment]
    [SampleableType P.Nullifier] (adv : Adversary P) (n : Nat) where
  primitives : PoolGame.PoolAssumptions (gamePrim P)
  hiding_nonneg : 0 ≤ primitives.εHiding
  length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n

theorem projectAdversary_length [SampleableType P.Salt] [DecidableEq P.Commitment]
    [SampleableType P.Nullifier] (setup : List (Tx P)) (adv : Adversary P) (n : Nat)
    (H : BoundAssumptions adv n) :
    PoolGame.Averaging.LengthBound (projectAdversary setup adv) n := by
  classical
  intro a ha
  change a ∈ support (adv.chooseWorlds >>= fun b =>
    if RecipientPair b.1 b.2.1 then
      pure (b.1.map (fun t => transferWitness t.body),
        b.2.1.map (fun t => transferWitness t.body), some (b.2.2, b.1))
    else pure ([], [], none)) at ha
  obtain ⟨b, hb, ha⟩ := (mem_support_bind_iff _ _ _).mp ha
  by_cases hp : RecipientPair b.1 b.2.1
  · simp only [hp, if_pos] at ha
    subst a
    simpa using H.length_bound b hb
  · simp only [hp] at ha
    subst a
    exact Nat.zero_le _

theorem advantage_le [SampleableType P.Salt] [DecidableEq P.Commitment]
    [SampleableType P.Nullifier] (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P) (n : Nat) (H : BoundAssumptions adv n) :
    advantage sup setup adv ≤ 2 * n * H.primitives.εHiding +
      rejectionProbability sup setup adv / 2 := by
  have ht := advantage_le_ideal_add_rejection sup setup adv
  have hb := PoolGame.Averaging.transferIndAdvantage_le H.primitives H.hiding_nonneg
    (projectAdversary setup adv) n (projectAdversary_length setup adv n H)
  have he : idealAdvantage setup adv = PoolGame.transferIndAdvantage (projectAdversary setup adv) := by
    unfold idealAdvantage PoolGame.transferIndAdvantage
    rw [ideal_eq_v1]
  rw [he] at ht
  linarith

end LeanShieldedPool.ChainGame
