import Mathlib.Tactic

/-!
# Shielded-pool state model (spec-level, DRAFT)

Abstract model of the on-chain state of 2/SHIELDED-POOL (Sections 4.4, 5.1, 5.2).
Cryptography is opaque: `PrimSpec` bundles the carrier types and the three
derivations of Section 5.1 with NO axioms relating them.

Every claim in this file is a `def ... : Prop` or plain data. No `sorry`,
no `axiom`.
-/

namespace LeanShieldedPool

open Classical

/-- Largest value of a `u128` note amount (Section 5.1, 5.3).
The spec requires every amount witness range-checked to this width and the
contract to reject any public amount at or above `2 ^ 128`. -/
def maxU128 : Nat := 2 ^ 128 - 1

/-- Range check of Section 5.3: an amount fits the note amount width. -/
def U128 (n : Nat) : Prop := n ≤ maxU128

/-- Recommended historical-root window size (Section 4.4). -/
def rootWindow : Nat := 100

/--
Opaque cryptographic profile (Sections 5.1, 5.4).

`commit` stands for `Poseidon4(token, amount, owner_pubkey, salt)`,
`nullify` for `Poseidon2(commitment, spending_key)` and
`derivePub` for `Poseidon1(spending_key)`.

No axiom constrains these functions. Collision resistance, hiding and
binding are deliberately absent: a later bead adds them as named
hypotheses on theorems, not as axioms (see `AXIOM-PROPOSALS.md`).
-/
structure PrimSpec where
  Token : Type
  Address : Type
  PubKey : Type
  SpendKey : Type
  Salt : Type
  Commitment : Type
  Nullifier : Type
  /-- `spending_pubkey = Poseidon1(spending_key)` (Section 5.1). -/
  derivePub : SpendKey → PubKey
  /-- `commitment = Poseidon4(token, amount, owner_pubkey, salt)` (Section 5.1). -/
  commit : Token → Nat → PubKey → Salt → Commitment
  /-- `nullifier = Poseidon2(commitment, spending_key)` (Section 5.1). -/
  nullify : Commitment → SpendKey → Nullifier

/-- A note (Section 5.1). `amount` is a `Nat` carrying an explicit `U128`
well-formedness side condition instead of a bitvector. -/
structure Note (P : PrimSpec) where
  token : P.Token
  amount : Nat
  ownerPubkey : P.PubKey
  salt : P.Salt

namespace Note

variable {P : PrimSpec}

/-- The note's commitment (Section 5.1). -/
def cm (n : Note P) : P.Commitment :=
  P.commit n.token n.amount n.ownerPubkey n.salt

/-- Note well-formedness: the amount is inside the `u128` range (Section 5.3). -/
def wf (n : Note P) : Prop := U128 n.amount

/-- Ballast is derived in-circuit from `amount == 0` (Section 5.3), never from
a free selector witness. -/
def isBallast (n : Note P) : Prop := n.amount = 0

/-- The note names the public key of `k` (Section 5.3, single spending-key
witness feeding both derivations). -/
def ownedBy (n : Note P) (k : P.SpendKey) : Prop := P.derivePub k = n.ownerPubkey

/-- The nullifier that spends this note under key `k` (Section 5.1). -/
def nf (n : Note P) (k : P.SpendKey) : P.Nullifier := P.nullify n.cm k

end Note

/--
On-chain state (Section 5.2), plus ghost accounting used only by the
statements of L3.

Real on-chain fields: the commitment tree (here the ordered leaf list, since
the tree is append-only and positional, Section 4.2 step 6), the historical
root window, the nullifier set, the per-token pool balance and the
supported-token set.

`minted` is the ghost leaf list: it stores the note behind each leaf, in
insertion order, so `liveValue` can be stated. On-chain only `leaves`
(the commitments) exists. `deposited` and `withdrawn` are ghost counters.

A historical root is abstracted to the number of leaves it commits to: a root
is a function of the leaf prefix, so "membership against a recent root" is
membership in a recorded prefix (task-directed abstraction).
-/
structure St (P : PrimSpec) where
  /-- Ghost: the notes behind the tree leaves, in insertion order. -/
  minted : List (Note P)
  /-- Ghost: commitments consumed by accepted spends, newest first (Section 6.2). -/
  spentCms : List P.Commitment
  /-- Historical-root window, newest first, at most `rootWindow` entries
  (Section 4.4). Each entry is a leaf-count snapshot. -/
  window : List Nat
  /-- Nullifier set, append-only (Section 5.2). -/
  nullifiers : List P.Nullifier
  /-- Per-token ERC-20 balance held by the pool contract. -/
  balance : P.Token → Nat
  /-- Supported-token set (Sections 3.2, 4.4). -/
  supported : P.Token → Prop
  /-- Ghost: total value deposited per token. -/
  deposited : P.Token → Nat
  /-- Ghost: total value withdrawn per token. -/
  withdrawn : P.Token → Nat

namespace St

variable {P : PrimSpec}

/-- The real commitment tree contents (Section 5.2). -/
def leaves (st : St P) : List P.Commitment := st.minted.map Note.cm

/-- `snap` is a root inside the bounded window (Section 4.4). -/
def rootInWindow (st : St P) (snap : Nat) : Prop := snap ∈ st.window

/-- Membership of `c` in the tree as it stood at windowed root `snap`
(Sections 5.3, 4.4). -/
def inTreeAt (st : St P) (snap : Nat) (c : P.Commitment) : Prop :=
  c ∈ st.leaves.take snap

/-- The nullifier is unspent (Sections 4.2, 4.3). -/
def fresh (st : St P) (x : P.Nullifier) : Prop := x ∉ st.nullifiers

/-- Push the root recorded after the final insertion of an operation, keeping
the window bounded (Section 4.4). -/
def pushWindow (w : List Nat) (n : Nat) : List Nat := (n :: w).take rootWindow

/-- Empty pool with a fixed supported-token set. The initial root (zero
leaves) is in the window. -/
def empty (P : PrimSpec) (sup : P.Token → Prop) : St P where
  minted := []
  spentCms := []
  window := [0]
  nullifiers := []
  balance := fun _ => 0
  supported := sup
  deposited := fun _ => 0
  withdrawn := fun _ => 0

/--
State well-formedness. Kept separate from `Step`: the guards of `Tx.lean`
are what the contract checks, this is what a later bead proves invariant.
-/
def wf (st : St P) : Prop :=
  st.window.length ≤ rootWindow ∧
  (∀ s ∈ st.window, s ≤ st.minted.length) ∧
  st.leaves.Nodup ∧
  st.nullifiers.Nodup ∧
  (∀ n ∈ st.minted, n.wf)

/--
A minted note is spent when an accepted spend has consumed its commitment,
recorded in the ghost `spentCms` (Section 6.2 "no double-spend"; the circuit
binds each nullifier to its input commitment, Section 5.1 line 305). A
nullifier collision can lock a note; it never marks it spent here.
-/
def spent (st : St P) (n : Note P) : Prop := n.cm ∈ st.spentCms

end St

/-- Add `d` to the entry of `t` in a per-token map. -/
noncomputable def bump {α : Type} (f : α → Nat) (t : α) (d : Nat) : α → Nat :=
  fun t' => if t' = t then f t' + d else f t'

/-- Subtract `d` from the entry of `t` in a per-token map (truncated `Nat`
subtraction; every use site guards `d ≤ f t`). -/
noncomputable def drop {α : Type} (f : α → Nat) (t : α) (d : Nat) : α → Nat :=
  fun t' => if t' = t then f t' - d else f t'

/-- Value of a note that counts toward the live pool value of token `t`. -/
noncomputable def noteValue {P : PrimSpec} (st : St P) (t : P.Token) (n : Note P) : Nat :=
  if n.token = t ∧ ¬ st.spent n then n.amount else 0

/-- Total value of unspent notes for token `t`. Used by the value-conservation
statement (Section 6.2). -/
noncomputable def liveValue {P : PrimSpec} (st : St P) (t : P.Token) : Nat :=
  (st.minted.map (noteValue st t)).sum

end LeanShieldedPool
