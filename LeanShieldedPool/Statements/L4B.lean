import LeanShieldedPool.Statements.L3
import LeanShieldedPool.Pool.Events

/-!
# L4 Tier B statements (plan section 1)

Promoted 2026-09-15 from worker drafts (bd-36e, bd-2sz) after review.
-/

namespace LeanShieldedPool

/--
**No theft**: authorization binding at the model level. For each operation
in a run, every run note with a consumed commitment belongs to that
operation's witness spending key, under `CryptoHyp`.

Cryptographic key secrecy and signature custody (spec Section 5.3, line
319; spec line 463) are out of model. This statement does not establish
them.
-/
def noTheft (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ tx ∈ txs, ∀ n ∈ runNotes txs, n.cm ∈ tx.consumes →
        ∃ k ∈ tx.keys, n.ownedBy k

/--
**Honest bookkeeping** (spec Section 4.4, lines 275-279): replaying the
event log of any accepted history reconstructs the commitment tree and
the nullifier set exactly. No cryptographic hypotheses.
-/
def eventReplayFaithful (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → replay (events txs) = (st.leaves, st.nullifiers)

end LeanShieldedPool
