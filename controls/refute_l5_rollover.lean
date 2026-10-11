-- Refutation control for `Epoch.frozenRootImmutability_proof`. This file
-- MUST BUILD. A rollover that RESETS older sealed lists instead of
-- preserving them breaks immutability: after sealing epoch 0's spend, one
-- further bad rollover erases the epoch-0 frozen list, where the real
-- model preserves it forever. The accepted mutated history reaches the
-- sealed state (the immutability Prop carries no `CryptoHyp`), and the
-- final theorem proves the explicit negation of the frozen Prop restated
-- over the mutated model.
import LeanShieldedPool.Proofs.Epoch

namespace LeanShieldedPool.Epoch
namespace NegRollover

open Examples

-- SEALING BROKEN: older frozen entries are dropped, not preserved.
def rolloverBad (st : St Toy) : St Toy :=
  { st with
    frozen := fun e => if e = st.currentEpoch then st.active else []
    active := []
    currentEpoch := st.currentEpoch + 1 }

/-- The step relation with the bad rollover. The three operations keep
their real guards and post-states; only the rollover case changes.
`ReachableRB` and `StepsRB` below mirror `Reachable` and `Candidates.Steps`
over this relation, specialized to the toy profile and its all-tokens
supported set. No other premise changes. -/
inductive StepRB : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepRB st (.deposit d) (d.post st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      d.guard st → StepRB st (.transfer d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepRB st (.withdraw d) (d.post st)
  | rollover {st : St Toy} : StepRB st .rollover (rolloverBad st)

inductive ReachableRB : St Toy → Prop where
  | empty : ReachableRB st0
  | step {st st' : St Toy} {tx : Tx Toy} :
      ReachableRB st → StepRB st tx st' → ReachableRB st'

inductive StepsRB : St Toy → List (Tx Toy) → St Toy → Prop where
  | nil (st : St Toy) : StepsRB st [] st
  | cons {before middle after : St Toy} {tx : Tx Toy} {txs : List (Tx Toy)} :
      StepRB before tx middle → StepsRB middle txs after →
      StepsRB before (tx :: txs) after

theorem g1 : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128]

theorem g2 : w0.guard st1 := by
  norm_num [WithdrawData.guard, st1, DepositData.post,
    St.empty, St.rootInWindow, St.inTreeAt, St.leaves,
    LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.wf, LeanShieldedPool.Note.wf,
    U128, maxU128, Note.cm, Note.nfE, SpendGuard, ChainFacts,
    InsertionFacts, AppendFresh, bump]

/-- Epoch 0's spend, sealed by the first (bad) rollover. At epoch 0 the
bad and real rollovers agree, because there is no older sealed list yet. -/
noncomputable abbrev sealed : St Toy := rolloverBad (w0.post st1)

/-- The mutated model REACHES the sealed state. The frozen Prop no longer
carries a reachability premise (it is a frame property of the step
relation), so the restatement below does not need this; it stays as evidence
that the counterexample state is one the mutated model produces. -/
theorem sealed_reachable : ReachableRB sealed :=
  ReachableRB.step (ReachableRB.step (ReachableRB.step ReachableRB.empty
    (StepRB.deposit g1)) (StepRB.withdraw g2)) StepRB.rollover

/-- `frozenRootImmutability`, restated over the mutated model, is FALSE:
the next bad rollover, from the sealed state, with an empty suffix, erases
the epoch-0 list that the real model preserves. The control passes only if
this refutation builds. -/
theorem frozen_erased_counterexample :
    ¬ ∀ (before after : St Toy) (suffix : List (Tx Toy)),
      StepsRB (rolloverBad before) suffix after →
        after.frozen before.currentEpoch = before.active ∧
        ∀ e, e < before.currentEpoch → after.frozen e = before.frozen e := by
  intro h
  have h2 := (h sealed (rolloverBad sealed) [] (StepsRB.nil _)).2 0
    (by norm_num [rolloverBad, WithdrawData.post, st1, DepositData.post, St.empty])
  norm_num [rolloverBad, WithdrawData.post, WithdrawData.nf, st1,
    DepositData.post, St.empty, Note.nfE, Note.cm] at h2

end NegRollover
end LeanShieldedPool.Epoch
