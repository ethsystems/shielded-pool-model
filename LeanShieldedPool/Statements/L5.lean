import LeanShieldedPool.Pool.Epoch
import LeanShieldedPool.Statements.L3

/-!
# L5 candidate statements

These definitions state the proof obligations. `Proofs/EpochBase.lean`
proves the base-pool reduction; `Proofs/Epoch.lean` proves the other
four theorems.
-/

namespace LeanShieldedPool.Epoch.Candidates

variable {P : PrimSpec}

def notes : Tx P → List (Note P)
  | .deposit d => [d.note]
  | .transfer d => [d.in1, d.in2, d.out1, d.out2]
  | .withdraw d => [d.note]
  | .rollover => []

/-- Both input slots count, including ballast. -/
def inputs : Tx P → List (Note P × P.SpendKey)
  | .deposit _ => []
  | .transfer d => [(d.in1, d.key), (d.in2, d.key)]
  | .withdraw d => [(d.note, d.key)]
  | .rollover => []

def runNotes (txs : List (Tx P)) : List (Note P) := txs.flatMap notes

def runKeys (txs : List (Tx P)) : List P.SpendKey :=
  (txs.flatMap inputs).map Prod.snd

/-- Binding assumptions concern only witnesses in this finite run. -/
structure CryptoHyp (P : PrimSpec) (txs : List (Tx P)) : Prop where
  commit_inj : ∀ n ∈ runNotes txs, ∀ n' ∈ runNotes txs,
    n.cm = n'.cm → n = n'
  derivePub_inj : ∀ k ∈ runKeys txs, ∀ k' ∈ runKeys txs,
    P.derivePub k = P.derivePub k' → k = k'

/-- The log spans every epoch. Rollover does not reset it. -/
def noteSpentAtMostOnce (txs : List (Tx P)) : Prop :=
  (txs.flatMap Tx.consumes).Nodup

def crossEpochNoDoubleSpend (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs → noteSpentAtMostOnce txs

/-- A suffix from a specific state, using exactly the skeleton's steps. -/
inductive Steps : St P → List (Tx P) → St P → Prop where
  | nil (st : St P) : Steps st [] st
  | cons {before middle after : St P} {tx : Tx P} {txs : List (Tx P)} :
      Step before tx middle → Steps middle txs after →
      Steps before (tx :: txs) after

/-- Seal the current list and preserve every sealed entry through any suffix.
A frame property of the step relation: it holds from any state, reachable or
not, because only rollover writes `frozen`. -/
def frozenRootImmutability (P : PrimSpec) : Prop :=
  ∀ (before after : St P) (suffix : List (Tx P)),
    Steps before.rollover suffix after →
      after.frozen before.currentEpoch = before.active ∧
      ∀ e, e < before.currentEpoch → after.frozen e = before.frozen e

/-- Exact order and sequential freshness, for one step and a whole epoch segment. -/
def canonicalAppend (P : PrimSpec) : Prop :=
  (∀ (before after : St P) (tx : Tx P),
    Step before tx after → tx ≠ .rollover →
      after.currentEpoch = before.currentEpoch ∧
      InsertionFacts (P := P) before.active (tx.spends before.currentEpoch) after.active) ∧
  (∀ (before after : St P) (txs : List (Tx P)),
    Steps before txs after → after.currentEpoch = before.currentEpoch →
      InsertionFacts (P := P) before.active
        (txs.flatMap (Tx.spends before.currentEpoch)) after.active)

/-- A fixed epoch selects the parent hash interface; it does not use the
unrelated inherited `commit` and `nullify` fields. -/
def basePrim (P : PrimSpec) : LeanShieldedPool.PrimSpec :=
  { P.toPrimSpec with
    commit := fun token amount owner salt => P.commitE token amount owner salt 0
    nullify := fun cm key => P.nfE cm key 0 }

def baseNote (n : Note P) : LeanShieldedPool.Note (basePrim P) :=
  { token := n.token, amount := n.amount, ownerPubkey := n.ownerPubkey, salt := n.salt }

/-- Rollover has no parent operation. The base-case premise excludes it. -/
def baseTxs : Tx P → List (LeanShieldedPool.Tx (basePrim P))
  | .deposit d => [.deposit { note := baseNote d.note, funding := d.funding }]
  | .transfer d => [.transfer {
      key := d.key, in1 := baseNote d.in1, in2 := baseNote d.in2,
      out1 := baseNote d.out1, out2 := baseNote d.out2, snapshot := d.snapshot }]
  | .withdraw d => [.withdraw {
      key := d.key, note := baseNote d.note, recipient := d.recipient, snapshot := d.snapshot }]
  | .rollover => []

/-- Parent updates prepend batches; epoch updates append them. Compare contents
by permutation while retaining exact commitment and accounting fields. -/
def BaseStateMatches (st : St P) (base : LeanShieldedPool.St (basePrim P)) : Prop :=
  st.currentEpoch = 0 ∧ (∀ e, st.frozen e = []) ∧
  base.minted = st.minted.map baseNote ∧ base.spentCms = st.spentCms ∧
  base.window = st.window ∧ base.nullifiers.Perm st.active ∧
  base.balance = st.balance ∧ base.supported = st.supported ∧
  base.deposited = st.deposited ∧ base.withdrawn = st.withdrawn

/-- A run without rollover refines the parent pool: it translates to an
accepted base run with matching state and transported hypotheses, and base
no-double-spend then gives the epoch consumption claim. The refinement is one
way: an epoch model that rejects honest base runs still satisfies it. This is
not the circuit's base case (extension spec 324-340). -/
def epochZeroRefinesBase (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → (∀ tx ∈ txs, tx ≠ .rollover) → CryptoHyp P txs →
      (∃ base : LeanShieldedPool.St (basePrim P),
        LeanShieldedPool.Run (P := basePrim P) sup (txs.flatMap baseTxs) base ∧
        BaseStateMatches st base ∧
        LeanShieldedPool.CryptoHyp (basePrim P) (txs.flatMap baseTxs) ∧
        (txs.flatMap baseTxs).flatMap LeanShieldedPool.Tx.consumes =
          txs.flatMap Tx.consumes) ∧
      (LeanShieldedPool.noDoubleSpend (basePrim P) → noteSpentAtMostOnce txs)

/-- One owner key accounts for every consumed witness of a commitment. This
does not extract separate recursive witnesses from proof bytes: the chain
key binding of the extension spec (336-337) is simplification 2 of
`Pool/Epoch.lean`, an assumption, not a consequence of this statement. -/
def chainKeyBinding (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ n ∈ runNotes txs, n.cm ∈ txs.flatMap Tx.consumes →
        ∃ key ∈ runKeys txs, n.ownedBy key ∧
          ∀ tx ∈ txs, ∀ input ∈ inputs tx, input.1.cm = n.cm →
            input.1 = n ∧ input.2 = key

end LeanShieldedPool.Epoch.Candidates
