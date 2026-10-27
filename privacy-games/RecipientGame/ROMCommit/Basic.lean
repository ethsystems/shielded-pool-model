import RecipientGame.ROMCommit.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.RecipientGame.ROMCommit
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}

structure Adversary (P : PrimSpec) (cap n : Nat) where
  State : Type
  choose : OracleComp (Spec P cap) (World P cap n × World P cap n × State)
  guess : State → List (PoolGame.Event (gamePrim P)) → OracleComp (Spec P cap) Bool

def QueryBound (adv : Adversary P cap n) (qc qg : Nat) : Prop :=
  adv.choose.IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) qc ∧
  ∀ s log, (adv.guess s log).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) qg

def worldBack (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ds : List (BoundedTransfer P cap)) : List (TransferData (oraclePrim P cap hp hn hc)) :=
  ds.map (fun d => rebaseTransfer hp hn hc d.val)

noncomputable def reduction (setup : List (Tx P)) (adv : Adversary P cap n)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    BatchAdversary (Message P cap) P.Salt P.Commitment (WithdrawGame.ROM.hashSpec P) (2*n) := by
  classical
  exact {
    State := Option (adv.State × Bool × List (PoolGame.Event (gamePrim P)) × List (PoolGame.TransferWitness (gamePrim P)))
    choose := do
      let (l,r,s) ← adv.choose
      let log ← history hn setup
      let wl ← witnesses l.val
      let wr ← witnesses r.val
      if PoolGame.LegalChallenge wl wr then do
        let b ← liftComp ($ᵗ Bool) (Spec P cap)
        let ds := if b then r else l
        pure (⟨messages ds.val,by rw [messages_length]; exact Nat.mul_le_mul_left 2 ds.property⟩,
          some (s,b,log,wl))
      else pure (⟨[],by simp⟩,none)
    guess := fun state cs => match state with
      | none => liftComp ($ᵗ Bool) (Spec P cap)
      | some (s,b,log,wl) => do
        let g ← adv.guess s (log ++ fill hn wl cs)
        pure (b == g) }

theorem reduction_bound (setup : List (Tx P)) (adv : Adversary P cap n)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (qc qg : Nat)
    (hq : QueryBound adv qc qg) :
    BatchQueryBound (reduction setup adv hn) (qc+4*setup.length+4*n) qg := by
  classical
  constructor
  · unfold reduction
    apply (isQueryBoundP_bind (n := qc) (m := 4*setup.length+4*n) hq.1 ?_).mono (by omega)
    intro x _
    apply isQueryBoundP_bind (history_bound hn setup)
    intro log _
    apply (isQueryBoundP_bind (n := 2*x.1.val.length) (m := 2*x.2.1.val.length)
      (witnesses_bound x.1.val) ?_).mono (by have hl := x.1.property; have hr := x.2.1.property; omega)
    intro wl _
    apply (isQueryBoundP_bind (n := 2*x.2.1.val.length) (m := 0) (witnesses_bound x.2.1.val) ?_).mono (by omega)
    intro wr _
    split
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (coins_bound (M := Message P cap) (S := P.Salt) (aux := WithdrawGame.ROM.hashSpec P) ($ᵗ Bool) 0)
    · simp
  · intro state cs
    cases state with
    | none => exact coins_bound _ qg
    | some x => simpa only [reduction, bind_pure_comp, isQueryBoundP_map_iff] using hq.2 x.1 _

abbrev Draw (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :=
  Option (adv.State × Bool × List (Tx (oraclePrim P cap hp hn hc)))

noncomputable def rejected (sup : P.Token → Prop) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) : Draw adv hp hn hc → Bool
  | none => false
  | some (_,_,txs) => (RecipientGame.runChecked (St.empty (oraclePrim P cap hp hn hc) sup) txs).isNone

def response (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    Draw adv hp hn hc → ProbComp Bool
  | none => $ᵗ Bool
  | some (s,b,txs) => do
    let g ← run (WithdrawGame.ROM.answers hp hn) hc
      (adv.guess s ((observerView txs).map (eventBack hp hn hc)))
    pure (b == g)

noncomputable def checkedResponse (sup : P.Token → Prop) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) (d : Draw adv hp hn hc) : ProbComp Bool :=
  if rejected sup adv hp hn hc d then $ᵗ Bool else response adv hp hn hc d

variable [SampleableType P.Salt]

noncomputable def atDraws (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) : ProbComp (Draw adv hp hn hc) := by
  classical
  exact do
    let (l,r,s) ← run (WithdrawGame.ROM.answers hp hn) hc adv.choose
    let left := worldBack hp hn hc l.val
    let right := worldBack hp hn hc r.val
    if RecipientGame.RecipientPair left right then do
      let b ← $ᵗ Bool
      let sampled ← RecipientGame.sampleWorld (if b then right else left)
      pure (some (s,b,setup.map (rebaseTx hp hn hc) ++ sampled.map Tx.transfer))
    else pure none

noncomputable def atUnguarded (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) : ProbComp Bool :=
  atDraws setup adv hp hn hc >>= response adv hp hn hc

noncomputable def atExperiment (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) : ProbComp Bool :=
  atDraws setup adv hp hn hc >>= checkedResponse sup adv hp hn hc

/-- The original RecipientGame publisher and recipient restriction, with an oracle-capable response. -/
theorem atExperiment_eq_publish2 (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    atExperiment sup setup adv hp hn hc = (by
      classical
      exact do
        let (l,r,s) ← run (WithdrawGame.ROM.answers hp hn) hc adv.choose
        let left := worldBack hp hn hc l.val
        let right := worldBack hp hn hc r.val
        if RecipientGame.RecipientPair left right then do
          let b ← $ᵗ Bool
          let result ← RecipientGame.publish2 (P := oraclePrim P cap hp hn hc) sup (setup.map (rebaseTx hp hn hc)) (if b then right else left)
          match result with
          | none => $ᵗ Bool
          | some log => do
            let g ← run (WithdrawGame.ROM.answers hp hn) hc (adv.guess s (log.map (eventBack hp hn hc)))
            pure (b == g)
        else $ᵗ Bool) := by
  classical
  simp only [atExperiment, atDraws, bind_assoc]
  apply bind_congr; intro x
  split
  · simp only [bind_assoc, RecipientGame.publish2]
    apply bind_congr; intro b
    apply bind_congr; intro sampled
    simp only [pure_bind, checkedResponse, rejected, response, RecipientGame.guardedLog]
    rcases Option.eq_none_or_eq_some (RecipientGame.runChecked (St.empty (oraclePrim P cap hp hn hc) sup)
      (setup.map (rebaseTx hp hn hc) ++ sampled.map Tx.transfer)) with he | ⟨st,he⟩
    · simp only [he, Option.isNone_none, if_true, Option.map_none]
    · simp only [he, Option.isNone_some, Bool.false_eq_true, if_false, Option.map_some]
  · simp [checkedResponse, rejected, response]

variable [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)] [SampleableType (Model.Table P cap)]

noncomputable def experiment (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
  let hc ← $ᵗ (Model.Table P cap)
  atExperiment sup setup adv hp hn hc

noncomputable def unguarded (setup : List (Tx P)) (adv : Adversary P cap n) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
  let hc ← $ᵗ (Model.Table P cap)
  atUnguarded setup adv hp hn hc

noncomputable def rejectionProbability (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) : ℝ := (Pr[= true | do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
  let hc ← $ᵗ (Model.Table P cap)
  let d ← atDraws setup adv hp hn hc
  pure (rejected sup adv hp hn hc d)]).toReal

noncomputable def advantage (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) : ℝ := |(Pr[= true | experiment sup setup adv]).toReal - 1/2|

theorem rejection_transport (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P cap n) :
    (experiment sup setup adv).boolDistAdvantage (unguarded setup adv) ≤
      rejectionProbability sup setup adv / 2 := by
  classical
  let draws := do
    let hp ← $ᵗ (P.SpendKey → P.PubKey)
    let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
    let hc ← $ᵗ (Model.Table P cap)
    let d ← atDraws setup adv hp hn hc
    pure (⟨hp,hn,hc,d⟩ : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) × Draw adv hp hn hc)
  let bad := fun d : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) ×
      Draw adv hp hn hc => rejected sup adv d.1 d.2.1 d.2.2.1 d.2.2.2
  let resp := fun d : (hp : P.SpendKey → P.PubKey) ×
      (hn : P.SpendKey × P.Commitment → P.Nullifier) × (hc : Model.Table P cap) ×
      Draw adv hp hn hc => response adv d.1 d.2.1 d.2.2.1 d.2.2.2
  have h := RecipientGame.rejection_distance_le draws bad resp
  unfold experiment atExperiment unguarded atUnguarded checkedResponse rejectionProbability
  simpa only [draws, bad, resp, bind_assoc, pure_bind] using h

end LeanShieldedPool.RecipientGame.ROMCommit
