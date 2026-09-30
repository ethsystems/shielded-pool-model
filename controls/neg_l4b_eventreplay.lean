-- EXPECT: unsolved goals
-- Negative control for `eventReplayFaithful_proof`.
-- A lossy replay that IGNORES withdraw events (a log without withdraw
-- nullifiers, violating spec 4.4 line 279: events must carry enough data
-- to reconstruct the spent set) cannot reconstruct the nullifier list of
-- the accepted deposit-transfer-withdraw run: it yields [5, 1] where the
-- state holds [10, 5, 1]. The proof attempt below must not close.
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

/-- The faithful-replay claim under the lossy log. FALSE: the withdraw
nullifier 10 is missing from the reconstruction. The control passes only
if this proof fails. -/
example :
    replayLossy (events [.deposit d0, .transfer t0, .withdraw w1]) =
      ((w1.post (t0.post (d0.post st0))).leaves,
       (w1.post (t0.post (d0.post st0))).nullifiers) := by
  norm_num [replayLossy, replayStepLossy, events, Tx.event, TransferData.nf1,
    TransferData.nf2, WithdrawData.nf, Note.nf, Note.cm, WithdrawData.post,
    TransferData.post, DepositData.post, St.empty, St.leaves]

end NegL4BEventReplay
end LeanShieldedPool
