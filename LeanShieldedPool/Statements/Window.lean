import LeanShieldedPool.Pool.Tx

/-!
# Root-window statements (issue #2)

The historical-root window holds only operation boundaries, and the root
after each operation's final insertion enters it (Section 4.4). An
honest owner can withdraw against any root in the window, and so against
the current root. No cryptographic hypotheses.
-/

namespace LeanShieldedPool

/-- **Window boundary** (Section 4.4, the half "intermediate roots do
not" enter). Every window entry is 0 (the empty tree) or the leaf count of
the state after some accepted prefix of the same history. The right side
does not read the window. This bounds what can enter; it does not say
that anything enters (a model that never pushes satisfies it). The other
half is `windowHead`. An intermediate root, such as the one banked
between the two transfer inserts before pocs-private#12, breaks it. -/
def windowBoundary (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → ∀ s ∈ st.window,
      s = 0 ∨
      ∃ (pre : List (Tx P)) (tx : Tx P) (st₀ st₁ : St P),
        pre ++ [tx] <+: txs ∧ Run sup pre st₀ ∧ Step st₀ tx st₁ ∧
        s = st₁.leaves.length

/-- **Window head** (Section 4.4, the half "the root recorded after the
final insertion of each operation enters the window"). After every
accepted history, the newest window entry is the current leaf count. -/
def windowHead (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → st.window.head? = some st.leaves.length

/-- **Honest withdrawal at a window root** (issue #2, liveness; Section
4.4, "accept proofs against any root in the window"). For any root `s`
in the window, the owner of a note that the pool minted before that root
(`n ∈ st.minted.take s`, the ghost note list behind the tree), with a
fresh nullifier, a nonzero amount and enough pool balance, has an
accepted withdrawal against `s`, and the pool pays out exactly the
amount. The commitment's membership at `s` and the note's `u128` range
are derived, not assumed. -/
def honestWithdrawWindow (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st →
    ∀ (k : P.SpendKey) (n : Note P) (r : P.Address) (s : Nat),
      s ∈ st.window → n ∈ st.minted.take s →
      n.ownedBy k → st.fresh (n.nf k) →
      n.amount ≠ 0 → n.amount ≤ st.balance n.token →
      ∃ st' : St P,
        Step st (.withdraw ⟨k, n, r, s⟩) st' ∧
        Run sup (txs ++ [.withdraw ⟨k, n, r, s⟩]) st' ∧
        st'.balance n.token + n.amount = st.balance n.token

/-- **Honest withdrawal at the current root** (issue #2, liveness). The
owner of a note that the pool minted (`n ∈ st.minted`, the ghost note
list behind the tree), with a fresh nullifier, a nonzero amount and
enough pool balance, has an accepted withdrawal against the current root
(`st.leaves.length`), and the pool pays out exactly the amount. The
note's `u128` range, the window membership of the current root and the
commitment's membership at that root are derived, not assumed. The
special case of `honestWithdrawWindow` at the newest window entry. -/
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
