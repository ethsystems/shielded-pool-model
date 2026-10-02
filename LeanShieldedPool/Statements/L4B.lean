import LeanShieldedPool.Statements.L3
import LeanShieldedPool.Pool.Events

/-!
# L4 Tier B statements (plan section 1)
-/

namespace LeanShieldedPool

/--
**Owner-key binding**: spending authorization at the model level. For each operation
in a run, every run note with a consumed commitment belongs to that
operation's witness spending key, under `CryptoHyp`.

Cryptographic key secrecy and signature custody (spec line 308; spec line
463) are out of model. This statement does not establish them. Two spec
theft routes are out of model under simplification 7: a deposit against
another address's allowance (342-343) and a relayer redirecting the
withdraw recipient (369).
-/
def spendRequiresOwnerKey (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → CryptoHyp P txs →
      ∀ tx ∈ txs, ∀ n ∈ runNotes txs, n.cm ∈ tx.consumes →
        ∃ k ∈ tx.keys, n.ownedBy k

/--
**Honest bookkeeping** (spec Section 4.4, line 279): replaying the
event log of any accepted history reconstructs the commitment tree and
the nullifier set exactly. No cryptographic hypotheses.
-/
def eventReplayFaithful (P : PrimSpec) : Prop :=
  ∀ (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P),
    Run sup txs st → replay (events txs) = (st.leaves, st.nullifiers)

end LeanShieldedPool
