import LeanShieldedPool.Pool.State

/-!
# Operations and the step relation (spec-level, DRAFT)

`deposit` (Section 4.1), `transfer` (Section 4.2, 2-in-2-out with a ballast
slot) and `withdraw` (Section 4.3) as a relation `Step : St → Tx → St → Prop`.

Each operation is split into a guard (`.guard`, what the contract and the
proof statement check) and a post-state (`.post`, the state update). The
guards encode the proof statements of Section 5.3 and the contract rules of
Section 4.4 that this abstraction can see.

No `sorry`, no `axiom`.
-/

namespace LeanShieldedPool

open Classical

variable {P : PrimSpec}

/-- Deposit payload (Section 4.1). Public inputs of the deposit statement
(Section 5.3): commitment, token, amount, funding address, payload
commitment. The payload commitment is not modelled. -/
structure DepositData (P : PrimSpec) where
  note : Note P
  /-- Public input, unconstrained in-circuit; the contract pulls tokens only
  from it (Section 5.3). -/
  funding : P.Address

/-- Transfer payload (Section 4.2). One spending key feeds both input
derivations, as Section 5.3 requires of the statement. -/
structure TransferData (P : PrimSpec) where
  key : P.SpendKey
  in1 : Note P
  /-- Only the second input may be a ballast (zero-value) note
  (Section 4.2). -/
  in2 : Note P
  out1 : Note P
  out2 : Note P
  /-- The public commitment root, as a windowed leaf-count snapshot. -/
  snapshot : Nat

/-- Withdraw payload (Section 4.3). Public inputs: nullifier, token, amount,
recipient, commitment root (Section 5.3). -/
structure WithdrawData (P : PrimSpec) where
  key : P.SpendKey
  note : Note P
  /-- Public input, unconstrained in-circuit; the contract routes funds to it
  (Section 5.3). -/
  recipient : P.Address
  snapshot : Nat

namespace TransferData

/-- First public nullifier (Section 5.3 clause 2). -/
def nf1 (d : TransferData P) : P.Nullifier := d.in1.nf d.key

/-- Second public nullifier, constrained even for a ballast input
(Section 5.3). -/
def nf2 (d : TransferData P) : P.Nullifier := d.in2.nf d.key

end TransferData

namespace WithdrawData

/-- The public nullifier (Section 5.3). -/
def nf (d : WithdrawData P) : P.Nullifier := d.note.nf d.key

end WithdrawData

/-- The three protocol operations (Section 4). -/
inductive Tx (P : PrimSpec) where
  | deposit : DepositData P → Tx P
  | transfer : TransferData P → Tx P
  | withdraw : WithdrawData P → Tx P

/-- Nullifiers consumed by an operation. Deposits consume none. -/
def Tx.spends : Tx P → List P.Nullifier
  | .deposit _ => []
  | .transfer d => [d.nf1, d.nf2]
  | .withdraw d => [d.nf]

/-- Commitments consumed by an operation (Section 5.3). -/
def Tx.consumes : Tx P → List P.Commitment
  | .deposit _ => []
  | .transfer d => [d.in1.cm, d.in2.cm]
  | .withdraw d => [d.note.cm]

namespace DepositData

/--
Deposit guard.

* supported token (Section 4.4);
* `amount ≠ 0`, zero-value deposits are tree-growth griefing (Section 4.4);
* amount inside `u128`, checked on-chain and in-circuit (Section 5.3);
* the commitment is not already in the tree (Section 4.4).

The deposit statement itself (`commitment == Poseidon4(...)`, Section 5.3
clause 1) holds by construction here: the model inserts `d.note.cm`, which is
that hash image, so insertion is reachable only from a constrained mint site
(Section 4.4).
-/
def guard (d : DepositData P) (st : St P) : Prop :=
  st.supported d.note.token ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount ∧
  d.note.cm ∉ st.leaves

/-- Deposit post-state: append the commitment, record the new root, pull
tokens (Section 4.1 step 6). -/
noncomputable def post (d : DepositData P) (st : St P) : St P :=
  { st with
    minted := st.minted ++ [d.note]
    window := St.pushWindow st.window (st.minted.length + 1)
    balance := bump st.balance d.note.token d.note.amount
    deposited := bump st.deposited d.note.token d.note.amount }

end DepositData

namespace TransferData

/--
Transfer guard (Sections 4.2 step 5, 4.4, 5.3).

* the public root is inside the window (Section 4.4);
* both inputs name the public key of the single spending-key witness
  (Section 5.3);
* the first input is a member of the tree at that root; the second input
  is a member unless it is ballast, and ballast is decided by
  `amount = 0`, never by a free selector (Sections 4.2, 5.3);
* both nullifiers are unspent and pairwise distinct (Section 4.2 step 5);
* token consistency over all four notes (Section 5.3 clause 5);
* every amount is range-checked to `u128` (Section 5.3);
* value conservation, input sum equals output sum (Section 5.3 clause 4);
* neither output commitment is already in the tree, and the two differ
  (Section 4.4).
-/
def guard (d : TransferData P) (st : St P) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧
  d.in2.ownedBy d.key ∧
  st.inTreeAt d.snapshot d.in1.cm ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  st.fresh d.nf1 ∧
  st.fresh d.nf2 ∧
  d.nf1 ≠ d.nf2 ∧
  d.in2.token = d.in1.token ∧
  d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  U128 d.in1.amount ∧
  U128 d.in2.amount ∧
  U128 d.out1.amount ∧
  U128 d.out2.amount ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount ∧
  d.out1.cm ∉ st.leaves ∧
  d.out2.cm ∉ st.leaves ∧
  d.out1.cm ≠ d.out2.cm

/-- Transfer post-state: mark both nullifiers spent, append both outputs in
public-input order, record the new root (Section 4.2 step 6). Balances do not
move: a transfer touches no ERC-20. -/
def post (d : TransferData P) (st : St P) : St P :=
  { st with
    minted := st.minted ++ [d.out1, d.out2]
    spentCms := d.in1.cm :: d.in2.cm :: st.spentCms
    window := St.pushWindow st.window (st.minted.length + 2)
    nullifiers := d.nf1 :: d.nf2 :: st.nullifiers }

end TransferData

namespace WithdrawData

/--
Withdraw guard (Sections 4.3 step 4, 5.3).

* the public root is inside the window, and the commitment is a member of the
  tree at that root;
* the note names the public key of the spending-key witness;
* the nullifier is unspent;
* `amount ≠ 0` (Section 4.4) and inside `u128` (Section 5.3);
* the pool holds enough of the token to pay out.
-/
def guard (d : WithdrawData P) (st : St P) : Prop :=
  st.rootInWindow d.snapshot ∧
  st.inTreeAt d.snapshot d.note.cm ∧
  d.note.ownedBy d.key ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount ∧
  d.note.amount ≤ st.balance d.note.token

/-- Withdraw post-state: mark spent, pay out. Nothing is inserted, so no new
root enters the window (Section 4.4). -/
noncomputable def post (d : WithdrawData P) (st : St P) : St P :=
  { st with
    nullifiers := d.nf :: st.nullifiers
    spentCms := d.note.cm :: st.spentCms
    balance := drop st.balance d.note.token d.note.amount
    withdrawn := bump st.withdrawn d.note.token d.note.amount }

end WithdrawData

/-- One accepted operation. A transaction that fails any guard reverts and is
not a step. -/
inductive Step : St P → Tx P → St P → Prop where
  | deposit {st : St P} {d : DepositData P} :
      d.guard st → Step st (.deposit d) (d.post st)
  | transfer {st : St P} {d : TransferData P} :
      d.guard st → Step st (.transfer d) (d.post st)
  | withdraw {st : St P} {d : WithdrawData P} :
      d.guard st → Step st (.withdraw d) (d.post st)

/-- States reachable from an empty pool with supported-token set `sup`. -/
inductive Reachable (sup : P.Token → Prop) : St P → Prop where
  | empty : Reachable sup (St.empty P sup)
  | step {st st' : St P} {tx : Tx P} :
      Reachable sup st → Step st tx st' → Reachable sup st'

/-- A full history: `Run sup txs st` means the accepted sequence `txs` takes
the empty pool to `st`. -/
inductive Run (sup : P.Token → Prop) : List (Tx P) → St P → Prop where
  | empty : Run sup [] (St.empty P sup)
  | step {txs : List (Tx P)} {st st' : St P} {tx : Tx P} :
      Run sup txs st → Step st tx st' → Run sup (txs ++ [tx]) st'

end LeanShieldedPool
