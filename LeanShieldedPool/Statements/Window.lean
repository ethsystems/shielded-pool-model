import LeanShieldedPool.Pool.Tx

/-!
# Root-window statements (issue #2)

The historical-root window holds only operation boundaries (Section 4.4).
No cryptographic hypotheses.
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

end LeanShieldedPool
