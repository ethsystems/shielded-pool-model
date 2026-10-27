import CommitROM.Model
import CommitROM.Batch
import RecipientGame.Rejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.ROMCommit
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap : Nat}

abbrev BoundedTransfer (P : PrimSpec) (cap : Nat) :=
  {d : TransferData P // d.out1.amount < cap ∧ d.out2.amount < cap}
abbrev World (P : PrimSpec) (cap n : Nat) :=
  {ds : List (BoundedTransfer P cap) // ds.length ≤ n}

def rebaseNote (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (d : Note P) :
    Note (oraclePrim P cap hp hn hc) := ⟨d.token,d.amount,d.ownerPubkey,d.salt⟩

def rebaseTransfer (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (d : TransferData P) :
    TransferData (oraclePrim P cap hp hn hc) :=
  ⟨d.key,rebaseNote hp hn hc d.in1,rebaseNote hp hn hc d.in2,
    rebaseNote hp hn hc d.out1,rebaseNote hp hn hc d.out2,d.snapshot⟩

def rebaseTx (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    Tx P → Tx (oraclePrim P cap hp hn hc)
  | .deposit d => .deposit ⟨rebaseNote hp hn hc d.note,d.funding⟩
  | .transfer d => .transfer (rebaseTransfer hp hn hc d)
  | .withdraw d => .withdraw ⟨d.key,rebaseNote hp hn hc d.note,d.recipient,d.snapshot⟩

def cmNote (d : Note P) : OracleComp (Spec P cap) P.Commitment :=
  Model.cm id (⟨d.token,d.amount,d.ownerPubkey,d.salt⟩ : WithdrawGame.NotePlan P P.PubKey)

theorem cmNote_bound (d : Note P) :
    (cmNote (cap := cap) d).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 1 :=
  Model.cm_bound _ _

theorem run_cmNote (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (d : Note P) :
    run (WithdrawGame.ROM.answers hp hn) hc (cmNote d) = pure (rebaseNote hp hn hc d).cm := by
  exact Model.run_cm hp hn hc id ⟨d.token,d.amount,d.ownerPubkey,d.salt⟩

def witness (d : TransferData P) : OracleComp (Spec P cap) (PoolGame.TransferWitness (gamePrim P)) := do
  let c₁ ← cmNote d.in1
  let c₂ ← cmNote d.in2
  pure ⟨c₁,c₂,d.key,d.key,d.out1.token,d.out1.amount,d.out1.ownerPubkey,
    d.out2.token,d.out2.amount,d.out2.ownerPubkey⟩

def witnesses : List (BoundedTransfer P cap) → OracleComp (Spec P cap) (List (PoolGame.TransferWitness (gamePrim P)))
  | [] => pure []
  | d :: ds => do let w ← witness d.val; let ws ← witnesses ds; pure (w :: ws)

def event (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    Tx P → OracleComp (Spec P cap) (PoolGame.Event (gamePrim P))
  | .deposit d => do let c ← cmNote d.note; pure (.deposit c)
  | .transfer d => do
    let c₁ ← cmNote d.in1; let c₂ ← cmNote d.in2
    let c₃ ← cmNote d.out1; let c₄ ← cmNote d.out2
    pure (.transfer (hn (d.key,c₁)) (hn (d.key,c₂)) c₃ c₄)
  | .withdraw d => do let c ← cmNote d.note; pure (.withdraw (hn (d.key,c)))

def history (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    List (Tx P) → OracleComp (Spec P cap) (List (PoolGame.Event (gamePrim P)))
  | [] => pure []
  | tx :: txs => do let e ← event hn tx; let es ← history hn txs; pure (e :: es)

theorem witness_bound (d : TransferData P) :
    (witness (cap := cap) d).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 2 := by
  unfold witness
  apply isQueryBoundP_bind (n := 1) (m := 1) (cmNote_bound d.in1)
  intro c₁ _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using cmNote_bound (cap := cap) d.in2

theorem witnesses_bound (ds : List (BoundedTransfer P cap)) :
    (witnesses ds).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) (2*ds.length) := by
  induction ds with
  | nil => simp [witnesses]
  | cons d ds ih =>
    simp only [witnesses, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_comm]
    apply isQueryBoundP_bind (witness_bound d.val)
    intro w _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

theorem event_bound (hn : P.SpendKey × P.Commitment → P.Nullifier) (tx : Tx P) :
    (event (cap := cap) hn tx).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 4 := by
  cases tx with
  | deposit d => simpa only [event, bind_pure_comp, isQueryBoundP_map_iff] using (cmNote_bound d.note).mono (by omega)
  | withdraw d => simpa only [event, bind_pure_comp, isQueryBoundP_map_iff] using (cmNote_bound d.note).mono (by omega)
  | transfer d =>
    apply isQueryBoundP_bind (n := 1) (m := 3) (cmNote_bound d.in1)
    intro c₁ _
    apply isQueryBoundP_bind (n := 1) (m := 2) (cmNote_bound d.in2)
    intro c₂ _
    apply isQueryBoundP_bind (n := 1) (m := 1) (cmNote_bound d.out1)
    intro c₃ _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using cmNote_bound (cap := cap) d.out2

theorem history_bound (hn : P.SpendKey × P.Commitment → P.Nullifier) (txs : List (Tx P)) :
    (history (cap := cap) hn txs).IsQueryBoundP (CommitROM.charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) (4*txs.length) := by
  induction txs with
  | nil => simp [history]
  | cons tx txs ih =>
    simp only [history, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_comm]
    apply isQueryBoundP_bind (event_bound hn tx)
    intro e _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

def witnessBack (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (w : PoolGame.TransferWitness (gamePrim (oraclePrim P cap hp hn hc))) :
    PoolGame.TransferWitness (gamePrim P) :=
  ⟨w.inCm1,w.inCm2,w.spendKey1,w.spendKey2,w.outToken1,w.outAmt1,w.outPk1,
    w.outToken2,w.outAmt2,w.outPk2⟩

theorem run_witness (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (d : TransferData P) :
    run (WithdrawGame.ROM.answers hp hn) hc (witness d) =
      pure (witnessBack hp hn hc (transferWitness (rebaseTransfer hp hn hc d))) := by
  unfold witness
  simp only [run, simulateQ_bind, simulateQ_pure]
  have h₁ := run_cmNote hp hn hc d.in1
  have h₂ := run_cmNote hp hn hc d.in2
  unfold run at h₁ h₂
  rw [h₁, pure_bind, h₂, pure_bind]
  rfl

theorem run_witnesses (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ds : List (BoundedTransfer P cap)) :
    run (WithdrawGame.ROM.answers hp hn) hc (witnesses ds) =
      pure ((ds.map (fun d => transferWitness (rebaseTransfer hp hn hc d.val))).map (witnessBack hp hn hc)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    unfold witnesses
    have hw := run_witness hp hn hc d.val
    simp only [run] at hw ih
    simp only [run, simulateQ_bind, simulateQ_pure, hw, ih, pure_bind]
    rfl

theorem run_event (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (tx : Tx P) :
    run (WithdrawGame.ROM.answers hp hn) hc (event hn tx) =
      pure (eventBack hp hn hc (gameEvent (Tx.event (rebaseTx hp hn hc tx)))) := by
  have hb {A B : Type} (oa : OracleComp (Spec P cap) A) (k : A → OracleComp (Spec P cap) B) :
      run (WithdrawGame.ROM.answers hp hn) hc (oa >>= k) =
        run (WithdrawGame.ROM.answers hp hn) hc oa >>= fun a => run (WithdrawGame.ROM.answers hp hn) hc (k a) :=
    simulateQ_bind _ _ _
  have hpure {A : Type} (a : A) : run (WithdrawGame.ROM.answers hp hn) hc (pure a) = pure a := rfl
  cases tx <;> simp only [event, hb, run_cmNote, pure_bind, hpure] <;> rfl

theorem run_history (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (txs : List (Tx P)) :
    run (WithdrawGame.ROM.answers hp hn) hc (history hn txs) =
      pure ((observerView (txs.map (rebaseTx hp hn hc))).map (eventBack hp hn hc)) := by
  induction txs with
  | nil => rfl
  | cons tx txs ih =>
    unfold history
    have he := run_event hp hn hc tx
    simp only [run] at he ih
    simp only [run, simulateQ_bind, simulateQ_pure, he, ih, pure_bind]
    rfl

def messages (ds : List (BoundedTransfer P cap)) : List (Message P cap) :=
  ds.flatMap (fun d => [(d.val.out1.token,⟨d.val.out1.amount,d.property.1⟩,d.val.out1.ownerPubkey),
    (d.val.out2.token,⟨d.val.out2.amount,d.property.2⟩,d.val.out2.ownerPubkey)])

theorem messages_length (ds : List (BoundedTransfer P cap)) : (messages ds).length = 2*ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [messages, List.flatMap_cons] at *; omega

/-- Fill two commitments per event, in the frozen observer's slot order. -/
def fill (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    List (PoolGame.TransferWitness (gamePrim P)) → List P.Commitment → List (PoolGame.Event (gamePrim P))
  | [], _ => []
  | w :: ws, c₁ :: c₂ :: cs => .transfer (hn (w.spendKey1,w.inCm1)) (hn (w.spendKey2,w.inCm2)) c₁ c₂ :: fill hn ws cs
  | _ :: _, _ => []

theorem fill_recipient (hn : P.SpendKey × P.Commitment → P.Nullifier)
    {ws₀ ws₁ : List (PoolGame.TransferWitness (gamePrim P))}
    (h : PoolGame.LegalChallenge ws₀ ws₁) (cs : List P.Commitment) :
    fill hn ws₀ cs = fill hn ws₁ cs := by
  induction h generalizing cs with
  | nil => rfl
  | @cons w₀ w₁ ws₀ ws₁ hw ht ih =>
    obtain ⟨h₁,h₂,h₃,h₄,_⟩ := hw
    cases cs with
    | nil => rfl
    | cons c₁ cs => cases cs with
      | nil => rfl
      | cons c₂ cs => simp only [fill, h₁, h₂, h₃, h₄, ih]

theorem recipient_back_iff (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ws₀ ws₁ : List (PoolGame.TransferWitness (gamePrim (oraclePrim P cap hp hn hc)))) :
    PoolGame.LegalChallenge (ws₀.map (witnessBack hp hn hc)) (ws₁.map (witnessBack hp hn hc)) ↔
      PoolGame.LegalChallenge ws₀ ws₁ := by
  simp only [PoolGame.LegalChallenge, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  rfl

end LeanShieldedPool.RecipientGame.ROMCommit
