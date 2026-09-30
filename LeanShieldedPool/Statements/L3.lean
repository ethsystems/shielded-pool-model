import LeanShieldedPool.Pool.Tx

namespace LeanShieldedPool

/-- Notes named by an operation's witness. -/
def Tx.notes {P : PrimSpec} : Tx P → List (Note P)
  | .deposit d => [d.note]
  | .transfer d => [d.in1, d.in2, d.out1, d.out2]
  | .withdraw d => [d.note]

/-- Spending keys used by an operation's witness. -/
def Tx.keys {P : PrimSpec} : Tx P → List P.SpendKey
  | .deposit _ => []
  | .transfer d => [d.key]
  | .withdraw d => [d.key]

def runNotes {P : PrimSpec} (txs : List (Tx P)) : List (Note P) := txs.flatMap Tx.notes
def runKeys {P : PrimSpec} (txs : List (Tx P)) : List P.SpendKey := txs.flatMap Tx.keys

/--
Cryptographic hypotheses, scoped to the witnesses of one run (Section 5.1).
`commit_inj` is Poseidon4 collision-freedom among the run's notes.
`derivePub_inj` is Poseidon1 collision-freedom among the run's spending keys.
Neither says anything about the hash outside the run.
-/
structure CryptoHyp (P : PrimSpec) (txs : List (Tx P)) : Prop where
  commit_inj : ∀ n ∈ runNotes txs, ∀ n' ∈ runNotes txs, n.cm = n'.cm → n = n'
  derivePub_inj : ∀ k ∈ runKeys txs, ∀ k' ∈ runKeys txs,
    P.derivePub k = P.derivePub k' → k = k'

/-- Idealised global form. Flagged: it asserts injectivity of finite hashes
and is kept only to show it implies `CryptoHyp P txs` for every run. -/
def CryptoHypGlobal (P : PrimSpec) : Prop :=
  (∀ n n' : Note P, n.cm = n'.cm → n = n') ∧ Function.Injective P.derivePub

/-- Commitments consumed by a run, in order, ballast included. -/
def spentCommitments {P : PrimSpec} (txs : List (Tx P)) : List P.Commitment :=
  txs.flatMap Tx.consumes

/-- **A note spends at most once** (Section 6.2, line 441), at the level the
chain sees: no commitment is consumed twice across the accepted history. -/
def noteSpentAtMostOnce {P : PrimSpec} (txs : List (Tx P)) : Prop :=
  (spentCommitments txs).Nodup

/-- Nullifier uniqueness (Section 5.2). The former `noDoubleSpend`, kept as
a lemma: it follows from the guards alone. -/
def nullifierUniqueness (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → (txs.flatMap Tx.spends).Nodup

/-- L3 theorem 1. -/
def noDoubleSpend (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs → noteSpentAtMostOnce txs

/-- L3 theorem 2 (Section 6.2, line 442). Live value counts unspent minted
notes; a note locked by a nullifier collision still counts as live. -/
def valueConservation (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ t : P.Token, st.deposited t = st.withdrawn t + liveValue st t

/-- Reduction reading of theorem 1: a double spend exhibits a collision among
the run's own witnesses. Classically equivalent to `noDoubleSpend`. -/
def doubleSpendExhibitsCollision (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → ¬ noteSpentAtMostOnce txs → ¬ CryptoHyp P txs

end LeanShieldedPool
