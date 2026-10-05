import LeanShieldedPool.Pool.Tx

/-!
# Epoch nullifiers (L5 trial skeleton)

Source: ethsystems/pocs-private at a04b8b38969dfc2ee64de47edee7e396454204a8,
`pocs/private-payment/shielded-pool-extension/SPEC.md`.
SHA-256: a05e86a53a00725486c319f3ca40b35bd77db954bc4b3c1b233085ec7e6a5da0.

Clause map: `PrimSpec` and `Note` follow Data Types; `St` and `rollover`
follow On-Chain State. `ChainFacts` follows Chain proof and Spend Circuit.
`InsertionFacts` follows Insertion Circuit and Cross-proof binding.
The three pool operations retain the guards and accounting of Pool/Tx.lean,
with the creation-epoch and nullifier changes in Diff vs Parent.

## WHAT-I-SIMPLIFIED

1. This is a semantic state machine, with witnesses in transaction data.
   `VerifierSoundness` names the assumed extraction of chain and insertion
   facts from accepted proofs. `Step` uses those facts directly. It does not
   prove verifier soundness or model proof bytes, recursion, VKs or circuits.
2. `ChainFacts` checks the entire half-open lifetime against actual frozen
   lists. This abstracts the accumulator, its contract comparison and root
   authentication. One supplied key derives every phantom and active value.
   The base owner guard still applies. Extracting a common key from separate
   recursive witnesses needs commitment binding and owner-key binding.
3. Lists represent tree contents, not on-chain storage. Frozen lists persist
   forever. Empty future entries mean unsealed epochs, not sealed empty roots.
   `InsertionFacts` retains sequential freshness and exact append order.
   It omits predecessor pointers, Merkle paths and the genesis sentinel.
   The real next slot corresponds to `active.length + 1`.
4. The insertion list is derived directly from the spend inputs in order.
   This abstracts the contract's cross-proof equality check and its checks
   of the current pre-root and count. Stale or mismatched proofs are not
   represented as transactions. Root binding and canonical encodings remain
   external assumptions.
5. Epochs are unbounded `Nat`, not u64. Rollover is an atomic operation with
   no clock or caller. Authorization, atomic calls and token behavior retain
   the parent model's scope limits. No implementation guarantee follows.
6. Hash functions remain opaque. `EpochDistinct` names collision freedom
   for one note and key over a bounded epoch interval. It is not built into
   the primitives or assumed over the entire domain of a finite hash.
   Commitment and key binding also need explicit hypotheses in future claims.
7. The note extends the parent note. State and operations use that note type,
   retaining the root window, ghost accounting and the parent's input rule:
   the first input must be a member; only a zero-amount second input may
   omit membership.
   Amount bounds and non-wrapping sums follow the parent abstraction.
   This file does not establish a refinement to the base pool.
8. PIR, privacy, events, liveness, proof costs and storage bounds are outside
   this skeleton. The examples check definitions, not L5 security theorems.
-/

namespace LeanShieldedPool.Epoch

open Classical

/-- Extended derivations; the inherited parent hashes are unused here. -/
structure PrimSpec extends LeanShieldedPool.PrimSpec where
  commitE : Token → Nat → PubKey → Salt → Nat → Commitment
  nfE : Commitment → SpendKey → Nat → Nullifier

structure Note (P : PrimSpec) extends LeanShieldedPool.Note P.toPrimSpec where
  epochCreated : Nat

namespace Note

variable {P : PrimSpec}

def cm (n : Note P) : P.Commitment :=
  P.commitE n.token n.amount n.ownerPubkey n.salt n.epochCreated

def nfE (n : Note P) (key : P.SpendKey) (epoch : Nat) : P.Nullifier :=
  P.nfE n.cm key epoch

def ownedBy (n : Note P) (key : P.SpendKey) : Prop :=
  n.toNote.ownedBy key

def isBallast (n : Note P) : Prop := n.toNote.isBallast

def wf (n : Note P) : Prop := n.toNote.wf

end Note

/-- Named, bounded hash hypothesis. No property of the primitives is imposed. -/
def EpochDistinct {P : PrimSpec} (n : Note P) (key : P.SpendKey)
    (through : Nat) : Prop :=
  ∀ e, n.epochCreated ≤ e → e ≤ through →
    ∀ e', n.epochCreated ≤ e' → e' ≤ through →
      e ≠ e' → n.nfE key e ≠ n.nfE key e'

structure St (P : PrimSpec) where
  minted : List (Note P)
  spentCms : List P.Commitment
  window : List Nat
  balance : P.Token → Nat
  supported : P.Token → Prop
  deposited : P.Token → Nat
  withdrawn : P.Token → Nat
  currentEpoch : Nat
  frozen : Nat → List P.Nullifier
  active : List P.Nullifier

namespace St

variable {P : PrimSpec}

def leaves (st : St P) : List P.Commitment := st.minted.map Note.cm

def rootInWindow (st : St P) (snapshot : Nat) : Prop := snapshot ∈ st.window

def inTreeAt (st : St P) (snapshot : Nat) (cm : P.Commitment) : Prop :=
  cm ∈ st.leaves.take snapshot

def spent (st : St P) (n : Note P) : Prop := n.cm ∈ st.spentCms

def empty (P : PrimSpec) (sup : P.Token → Prop) : St P where
  minted := []
  spentCms := []
  window := [0]
  balance := fun _ => 0
  supported := sup
  deposited := fun _ => 0
  withdrawn := fun _ => 0
  currentEpoch := 0
  frozen := fun _ => []
  active := []

/-- State checks only. Preservation is not asserted in this trial. -/
def wf (st : St P) : Prop :=
  st.window.length ≤ rootWindow ∧
  (∀ s ∈ st.window, s ≤ st.minted.length) ∧
  st.leaves.Nodup ∧ st.active.Nodup ∧
  (∀ e, (st.frozen e).Nodup) ∧
  (∀ e, st.currentEpoch ≤ e → st.frozen e = []) ∧
  (∀ n ∈ st.minted, n.wf ∧ n.epochCreated ≤ st.currentEpoch)

/-- Seal only the current epoch. All other fields and frozen entries persist. -/
def rollover (st : St P) : St P :=
  { st with
    frozen := fun e => if e = st.currentEpoch then st.active else st.frozen e
    active := []
    currentEpoch := st.currentEpoch + 1 }

end St

variable {P : PrimSpec}

/-- Caught-up chain: no missing initial or final epoch. The base interval is empty. -/
def ChainFacts (st : St P) (n : Note P) (key : P.SpendKey) : Prop :=
  n.epochCreated ≤ st.currentEpoch ∧
  ∀ e, n.epochCreated ≤ e → e < st.currentEpoch →
    n.nfE key e ∉ st.frozen e

/-- Each insertion checks the list produced by the preceding insertion. -/
def AppendFresh (before : List P.Nullifier) : List P.Nullifier → Prop
  | [] => True
  | nf :: rest => nf ∉ before ∧ AppendFresh (before ++ [nf]) rest

/-- Exact content facts attested by an insertion proof, including append order. -/
def InsertionFacts (before inserted after : List P.Nullifier) : Prop :=
  AppendFresh (P := P) before inserted ∧ after = before ++ inserted

/-- A single spend checks frozen history and the current active list. -/
def SpendGuard (st : St P) (n : Note P) (key : P.SpendKey) : Prop :=
  ChainFacts st n key ∧
  InsertionFacts (P := P) st.active [n.nfE key st.currentEpoch]
    (st.active ++ [n.nfE key st.currentEpoch])

/-- Acceptance interfaces after public-input binding and witness extraction.
These are abstract relations, not implementations of cryptographic verifiers. -/
structure Verifiers (P : PrimSpec) where
  chainAccepted : St P → Note P → P.SpendKey → Prop
  insertionAccepted : List P.Nullifier → List P.Nullifier → List P.Nullifier → Prop

/-- Named assumption for interpreting accepted proofs as the facts used below.
Chain acceptance includes binding to the actual frozen history and the spend key.
No completeness or soundness proof is supplied. Parent verifier assumptions remain. -/
structure VerifierSoundness (V : Verifiers P) : Prop where
  chain : ∀ st n key, V.chainAccepted st n key → ChainFacts st n key
  insertion : ∀ before inserted after,
    V.insertionAccepted before inserted after →
      InsertionFacts (P := P) before inserted after

structure DepositData (P : PrimSpec) where
  note : Note P
  funding : P.Address

structure TransferData (P : PrimSpec) where
  key : P.SpendKey
  in1 : Note P
  in2 : Note P
  out1 : Note P
  out2 : Note P
  snapshot : Nat

structure WithdrawData (P : PrimSpec) where
  key : P.SpendKey
  note : Note P
  recipient : P.Address
  snapshot : Nat

namespace DepositData

def guard (d : DepositData P) (st : St P) : Prop :=
  st.supported d.note.token ∧ d.note.amount ≠ 0 ∧ d.note.wf ∧
  d.note.cm ∉ st.leaves ∧ d.note.epochCreated = st.currentEpoch

noncomputable def post (d : DepositData P) (st : St P) : St P :=
  { st with
    minted := st.minted ++ [d.note]
    window := LeanShieldedPool.St.pushWindow st.window (st.minted.length + 1)
    balance := bump st.balance d.note.token d.note.amount
    deposited := bump st.deposited d.note.token d.note.amount }

end DepositData

namespace TransferData

/-- The same ordered list feeds the spend guard, insertion facts and post-state. -/
def nullifiers (d : TransferData P) (epoch : Nat) : List P.Nullifier :=
  [d.in1.nfE d.key epoch, d.in2.nfE d.key epoch]

def guard (d : TransferData P) (st : St P) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧ d.in2.ownedBy d.key ∧
  st.inTreeAt d.snapshot d.in1.cm ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  ChainFacts st d.in1 d.key ∧ ChainFacts st d.in2 d.key ∧
  InsertionFacts (P := P) st.active (d.nullifiers st.currentEpoch)
    (st.active ++ d.nullifiers st.currentEpoch) ∧
  d.in2.token = d.in1.token ∧ d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  d.in1.wf ∧ d.in2.wf ∧ d.out1.wf ∧ d.out2.wf ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount ∧
  d.out1.cm ∉ st.leaves ∧ d.out2.cm ∉ st.leaves ∧ d.out1.cm ≠ d.out2.cm ∧
  d.out1.epochCreated = st.currentEpoch ∧ d.out2.epochCreated = st.currentEpoch

def post (d : TransferData P) (st : St P) : St P :=
  { st with
    minted := st.minted ++ [d.out1, d.out2]
    spentCms := d.in1.cm :: d.in2.cm :: st.spentCms
    window := LeanShieldedPool.St.pushWindow st.window (st.minted.length + 2)
    active := st.active ++ d.nullifiers st.currentEpoch }

end TransferData

namespace WithdrawData

def nf (d : WithdrawData P) (epoch : Nat) : P.Nullifier := d.note.nfE d.key epoch

def guard (d : WithdrawData P) (st : St P) : Prop :=
  st.rootInWindow d.snapshot ∧ st.inTreeAt d.snapshot d.note.cm ∧
  d.note.ownedBy d.key ∧ SpendGuard st d.note d.key ∧
  d.note.amount ≠ 0 ∧ d.note.wf ∧ d.note.amount ≤ st.balance d.note.token

noncomputable def post (d : WithdrawData P) (st : St P) : St P :=
  { st with
    active := st.active ++ [d.nf st.currentEpoch]
    spentCms := d.note.cm :: st.spentCms
    balance := drop st.balance d.note.token d.note.amount
    withdrawn := bump st.withdrawn d.note.token d.note.amount }

end WithdrawData

inductive Tx (P : PrimSpec) where
  | deposit : DepositData P → Tx P
  | transfer : TransferData P → Tx P
  | withdraw : WithdrawData P → Tx P
  | rollover : Tx P

def Tx.spends (epoch : Nat) : Tx P → List P.Nullifier
  | .deposit _ => []
  | .transfer d => d.nullifiers epoch
  | .withdraw d => [d.nf epoch]
  | .rollover => []

def Tx.consumes : Tx P → List P.Commitment
  | .deposit _ => []
  | .transfer d => [d.in1.cm, d.in2.cm]
  | .withdraw d => [d.note.cm]
  | .rollover => []

/-- Ideal accepted operations. This is not a claim about an actual verifier. -/
inductive Step : St P → Tx P → St P → Prop where
  | deposit {st : St P} {d : DepositData P} :
      d.guard st → Step st (.deposit d) (d.post st)
  | transfer {st : St P} {d : TransferData P} :
      d.guard st → Step st (.transfer d) (d.post st)
  | withdraw {st : St P} {d : WithdrawData P} :
      d.guard st → Step st (.withdraw d) (d.post st)
  | rollover {st : St P} : Step st .rollover st.rollover

inductive Reachable (sup : P.Token → Prop) : St P → Prop where
  | empty : Reachable sup (St.empty P sup)
  | step {st st' : St P} {tx : Tx P} :
      Reachable sup st → Step st tx st' → Reachable sup st'

inductive Run (sup : P.Token → Prop) : List (Tx P) → St P → Prop where
  | empty : Run sup [] (St.empty P sup)
  | step {txs : List (Tx P)} {st st' : St P} {tx : Tx P} :
      Run sup txs st → Step st tx st' → Run sup (txs ++ [tx]) st'

namespace Examples

/-- Tuples expose the epoch argument. This is not a cryptographic instance. -/
abbrev Toy : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Unit
  SpendKey := Unit
  Salt := Nat
  Commitment := Nat × Nat × Nat
  Nullifier := (Nat × Nat × Nat) × Nat
  derivePub := fun _ => ()
  commit := fun _ amount _ salt => (amount, salt, 0)
  nullify := fun cm _ => (cm, 0)
  commitE := fun _ amount _ salt epoch => (amount, salt, epoch)
  nfE := fun cm _ epoch => (cm, epoch)

abbrev note (amount salt epoch : Nat) : Note Toy :=
  { token := (), amount := amount, ownerPubkey := (), salt := salt,
    epochCreated := epoch }

abbrev st0 : St Toy := St.empty Toy (fun _ => True)
abbrev d0 : DepositData Toy := ⟨note 5 0 0, ()⟩
noncomputable def st1 : St Toy := d0.post st0

abbrev t0 : TransferData Toy :=
  ⟨(), note 5 0 0, note 0 1 0, note 3 2 0, note 2 3 0, 1⟩
abbrev w0 : WithdrawData Toy := ⟨(), note 5 0 0, (), 1⟩

example : st0.wf := by
  norm_num [St.wf, St.empty, St.leaves, rootWindow]

example : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128]

example : st1.wf := by
  norm_num [st1, DepositData.post, St.wf, St.empty, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128]

example : t0.guard st1 := by
  norm_num [TransferData.guard, TransferData.nullifiers, st1, DepositData.post,
    St.empty, St.rootInWindow, St.inTreeAt, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.isBallast, LeanShieldedPool.Note.isBallast,
    Note.wf, LeanShieldedPool.Note.wf, U128, maxU128, Note.cm, Note.nfE,
    ChainFacts, InsertionFacts, AppendFresh]
  decide

example : w0.guard st1 := by
  norm_num [WithdrawData.guard, st1, DepositData.post,
    St.empty, St.rootInWindow, St.inTreeAt, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.wf, LeanShieldedPool.Note.wf,
    U128, maxU128, Note.cm, Note.nfE, SpendGuard, ChainFacts,
    InsertionFacts, AppendFresh, bump]

example : (w0.post st1).rollover.wf := by
  norm_num [St.wf, WithdrawData.post, WithdrawData.nf, st1, DepositData.post,
    St.rollover, St.empty, St.leaves, LeanShieldedPool.St.pushWindow,
    rootWindow, Note.wf, LeanShieldedPool.Note.wf, U128, maxU128]
  constructor
  · intro e
    split_ifs <;> decide
  · intro e he
    omega

/-- An old note can spend after rollover if its frozen history is clear. -/
example : w0.guard st1.rollover := by
  norm_num [WithdrawData.guard, st1, DepositData.post, St.rollover,
    St.empty, St.rootInWindow, St.inTreeAt, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.wf, LeanShieldedPool.Note.wf,
    U128, maxU128, Note.cm, Note.nfE, SpendGuard, ChainFacts,
    InsertionFacts, AppendFresh, bump]

example : (note 5 0 0).cm ≠ (note 5 0 1).cm := by decide

example : EpochDistinct (note 5 0 0) () 2 := by
  intro e _ _ e' _ _ hne heq
  exact hne (congrArg Prod.snd heq)

/-- A future creation epoch cannot bypass the history interval. -/
example : ¬ SpendGuard st0 (note 5 0 1) () := by
  norm_num [SpendGuard, ChainFacts, St.empty]

/-- Duplicate inputs fail the second insertion even when the pre-list is empty. -/
example : ¬ InsertionFacts (P := Toy) [] [((5, 0, 0), 0), ((5, 0, 0), 0)]
    [((5, 0, 0), 0), ((5, 0, 0), 0)] := by
  norm_num [InsertionFacts, AppendFresh]

example : (w0.post st1).rollover.frozen 0 = [((5, 0, 0), 0)] := rfl

example : (w0.post st1).rollover.active = [] := rfl

example : (w0.post st1).rollover.currentEpoch = 1 := rfl

example : (w0.post st1).rollover.rollover.frozen 0 = [((5, 0, 0), 0)] := rfl

/-- The changed active nullifier does not erase the spent creation-epoch entry. -/
example : ¬ SpendGuard (w0.post st1).rollover w0.note w0.key := by
  intro h
  have hmissing := h.1.2 0 (by decide) (by decide)
  exact hmissing (by decide)

end Examples

end LeanShieldedPool.Epoch
