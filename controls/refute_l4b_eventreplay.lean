-- Refutation control for `eventReplayFaithful_proof`. This file MUST BUILD.
-- A lossy replay that IGNORES withdraw events (a log without withdraw
-- nullifiers, violating spec 4.4 line 279: events must carry enough data
-- to reconstruct the spent set) cannot reconstruct the nullifier list of
-- the accepted deposit-transfer-withdraw run: it yields [5, 1] where the
-- state holds [10, 5, 1]. The mutation is in the replay, so the run is the
-- real one; the final theorem proves the explicit negation of the frozen
-- Prop with the lossy replay in place of `replay`.
import LeanShieldedPool.Proofs.EventReplay

namespace LeanShieldedPool
namespace NegL4BEventReplay

open NonVacuity EventLogNonVacuity

-- REPLAY WEAKENED: withdraw events carry no data.
def replayStepLossy (state : List Toy.Commitment × List Toy.Nullifier) :
    Event Toy → List Toy.Commitment × List Toy.Nullifier
  | .deposit cm => (state.1 ++ [cm], state.2)
  | .transfer nf1 nf2 out1 out2 => (state.1 ++ [out1, out2], nf1 :: nf2 :: state.2)
  | .withdraw _ => state

def replayLossy (log : List (Event Toy)) : List Toy.Commitment × List Toy.Nullifier :=
  log.foldl replayStepLossy ([], [])

/-- `eventReplayFaithful`, with the lossy replay, is FALSE on the accepted
deposit-transfer-withdraw run: the withdraw nullifier 10 is missing from
the reconstruction. The control passes only if this refutation builds. -/
theorem replay_counterexample :
    ¬ ∀ (sup : Toy.Token → Prop) (txs : List (Tx Toy)) (st : St Toy),
      Run sup txs st → replayLossy (events txs) = (st.leaves, st.nullifiers) := by
  intro h
  have hc := h _ _ _ all_operations_run
  norm_num [replayLossy, replayStepLossy, events, Tx.event, TransferData.nf1,
    TransferData.nf2, WithdrawData.nf, Note.nf, Note.cm, WithdrawData.post,
    TransferData.post, DepositData.post, St.empty, St.leaves] at hc

end NegL4BEventReplay
end LeanShieldedPool
