-- Refutation control for `Epoch.spendableAfterRollover_proof`. This file
-- MUST BUILD. A rollover that also RESETS the root window to `[0]` breaks
-- liveness: after the prefix deposit and transfer, the first transfer
-- output is owned, funded and has a clear history, but the current root
-- is no longer in the window, so the owner's withdrawal at that root fails
-- the guard and has no step. The real rollover keeps the window. The
-- mutated model reaches the state by the real deposit and transfer steps
-- (the Prop carries no `CryptoHyp`), and the final theorem proves the
-- explicit negation of the frozen Prop restated over the mutated model.
import LeanShieldedPool.Proofs.Epoch

namespace LeanShieldedPool.Epoch
namespace NegLiveness

open Examples

-- WINDOW RESET: the rollover also forgets every recorded root but 0.
def rolloverBad (st : St Toy) : St Toy :=
  { st with
    frozen := fun e => if e = st.currentEpoch then st.active else st.frozen e
    active := []
    currentEpoch := st.currentEpoch + 1
    window := [0] }

/-- The step relation with the bad rollover. The three operations keep
their real guards and post-states. -/
inductive StepRW : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepRW st (.deposit d) (d.post st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      d.guard st → StepRW st (.transfer d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepRW st (.withdraw d) (d.post st)
  | rollover {st : St Toy} : StepRW st .rollover (rolloverBad st)

inductive RunRW : List (Tx Toy) → St Toy → Prop where
  | empty : RunRW [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunRW txs st → StepRW st tx st' → RunRW (txs ++ [tx]) st'

theorem g1 : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128]

theorem g2 : t0.guard st1 := by
  norm_num [TransferData.guard, TransferData.nullifiers, st1, DepositData.post,
    St.empty, St.rootInWindow, St.inTreeAt, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.isBallast, LeanShieldedPool.Note.isBallast,
    Note.wf, LeanShieldedPool.Note.wf, U128, maxU128, Note.cm, Note.nfE,
    ChainFacts, InsertionFacts, AppendFresh]
  decide

/-- The mutated model REACHES the pre-rollover state by real steps. -/
theorem prefix_run : RunRW [.deposit d0, .transfer t0] (t0.post st1) :=
  RunRW.step (RunRW.step RunRW.empty (StepRW.deposit g1)) (StepRW.transfer g2)

/-- The first transfer output: owned, funded, created in epoch 0. -/
abbrev out : Note Toy := note 3 2 0

theorem out_minted : out ∈ (t0.post st1).minted := by
  norm_num [TransferData.post, st1, DepositData.post, St.empty]

theorem out_funded : out.amount ≤ (t0.post st1).balance out.token := by
  norm_num [TransferData.post, st1, DepositData.post, St.empty, bump]

/-- The output's history is clear: its only in-range nullifier, for epoch 0,
is not in the active list. -/
theorem out_clear : ∀ e, out.epochCreated ≤ e → e ≤ (t0.post st1).currentEpoch →
    out.nfE () e ∉ (if e = (t0.post st1).currentEpoch then (t0.post st1).active
      else (t0.post st1).frozen e) := by
  intro e _ he
  have h0 : e = 0 := Nat.le_zero.mp he
  subst h0
  decide

/-- `spendableAfterRollover`, restated over the mutated model, is FALSE: the
window reset drops the current root, so the owner's withdrawal at that root
fails `rootInWindow`. The control passes only if this refutation builds. -/
theorem liveness_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunRW txs st →
      ∀ (k : Toy.SpendKey) (n : Note Toy) (r : Toy.Address),
        n ∈ st.minted → n.ownedBy k → n.amount ≠ 0 →
        n.amount ≤ st.balance n.token →
        (∀ e, n.epochCreated ≤ e → e ≤ st.currentEpoch →
          n.nfE k e ∉ (if e = st.currentEpoch then st.active else st.frozen e)) →
        WithdrawData.guard ⟨k, n, r, st.leaves.length⟩ (rolloverBad st) ∧
        ∃ st', StepRW (rolloverBad st) (.withdraw ⟨k, n, r, st.leaves.length⟩) st' := by
  intro h
  have hg := (h _ _ prefix_run () out () out_minted rfl (by decide) out_funded out_clear).1
  have hwin : (t0.post st1).leaves.length ∈ (rolloverBad (t0.post st1)).window := hg.1
  norm_num [rolloverBad, TransferData.post, st1, DepositData.post, St.empty, St.leaves] at hwin

end NegLiveness
end LeanShieldedPool.Epoch
