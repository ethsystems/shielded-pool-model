import LeanShieldedPool.Statements.L3

/-!
# L4 Tier A statements (plan section 1)

Consequences of the L3 model: no minting, no over-withdrawal, and the two
supporting identities. `poolSolvency` and `noOverWithdrawal` need no
cryptographic hypotheses: they follow from the guards and post-states
alone. `noMinting` and `balanceIsLiveValue` inherit the run-scoped
`CryptoHyp` through value conservation.
-/

namespace LeanShieldedPool

/-- **Pool solvency** (Section 4.4: the withdraw guard requires the pool to
hold the payout). For every token, contract balance plus total withdrawn
equals total deposited. No cryptographic hypotheses. -/
def poolSolvency (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → ∀ t : P.Token, st.balance t + st.withdrawn t = st.deposited t

/-- **No over-withdrawal** (Section 6.2): total withdrawn never exceeds
total deposited. No cryptographic hypotheses. -/
def noOverWithdrawal (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → ∀ t : P.Token, st.withdrawn t ≤ st.deposited t

/-- **No minting** (Section 6.2): the live (unspent) note value never
exceeds total deposits, under the run-scoped `CryptoHyp`. -/
def noMinting (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ t : P.Token, liveValue st t ≤ st.deposited t

/-- The contract balance equals the live note value, under the run-scoped
`CryptoHyp`. Solvency plus value conservation. -/
def balanceIsLiveValue (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ t : P.Token, st.balance t = liveValue st t

end LeanShieldedPool
