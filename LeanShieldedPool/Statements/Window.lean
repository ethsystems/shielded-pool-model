import LeanShieldedPool.Pool.Tx

/-!
# Root-window statements (issue #2)

The historical-root window holds only operation boundaries (Section 4.4),
and an honest owner can withdraw against the current root. No
cryptographic hypotheses.
-/

namespace LeanShieldedPool

/-- **Window boundary** (Section 4.4: a root enters the window only after
an operation's final insertion). Every window entry is 0 (the empty tree)
or the leaf count of the state after some accepted prefix of the same
history. The right side does not read the window. An intermediate root,
such as the one banked between the two transfer inserts before
pocs-private#12, breaks it. -/
def windowBoundary (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → ∀ s ∈ st.window,
      s = 0 ∨
      ∃ (pre : List (Tx P)) (tx : Tx P) (st₀ st₁ : St P),
        pre ++ [tx] <+: txs ∧ Run sup pre st₀ ∧ Step st₀ tx st₁ ∧
        s = st₁.leaves.length

/-- **Honest withdrawal** (issue #2, liveness). The owner of a note in the
current tree, with a fresh nullifier, a nonzero amount and enough pool
balance, has an accepted withdrawal against the current root
(`st.leaves.length`), and the pool pays out exactly the amount. The note's
`u128` range, the window membership of the current root and the
commitment's membership at that root are derived, not assumed. -/
def honestWithdraw (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st →
    ∀ (k : P.SpendKey) (n : Note P) (r : P.Address),
      n ∈ st.minted → n.ownedBy k → st.fresh (n.nf k) →
      n.amount ≠ 0 → n.amount ≤ st.balance n.token →
      ∃ st' : St P,
        Step st (.withdraw ⟨k, n, r, st.leaves.length⟩) st' ∧
        Run sup (txs ++ [.withdraw ⟨k, n, r, st.leaves.length⟩]) st' ∧
        st'.balance n.token + n.amount = st.balance n.token

end LeanShieldedPool
