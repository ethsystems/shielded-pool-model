-- Refutation control for `Epoch.crossEpochNoDoubleSpend_proof`. This file
-- MUST BUILD. The withdraw guard with the ChainFacts (frozen-history)
-- conjunct REMOVED accepts spending the same note in epoch 0 and again in
-- epoch 1: the epoch-1 nullifier differs, active-list freshness passes,
-- and only the frozen-history check knows about the old spend. The real
-- model rejects this exact second spend: `real_guard_rejects` below shows
-- the real withdraw guard fails at the `ChainFacts` conjunct for epoch 0.
-- The accepted history consumes
-- one commitment twice and satisfies the epoch `CryptoHyp` (proven below),
-- so the final theorem proves the explicit negation of the frozen Prop
-- restated over the mutated model.
import LeanShieldedPool.Proofs.Epoch

namespace LeanShieldedPool.Epoch
namespace NegChainFacts

open Examples

/-- Second deposited note keeps the pool solvent for the second spend. -/
abbrev dB : DepositData Toy := ⟨note 5 4 0, ()⟩

-- GUARD REMOVED: no `ChainFacts st d.note d.key`; active freshness kept.
def guardNoChain (d : WithdrawData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧ st.inTreeAt d.snapshot d.note.cm ∧
  d.note.ownedBy d.key ∧
  InsertionFacts (P := Toy) st.active [d.nf st.currentEpoch]
    (st.active ++ [d.nf st.currentEpoch]) ∧
  d.note.amount ≠ 0 ∧ d.note.wf ∧ d.note.amount ≤ st.balance d.note.token

/-- The mutated step relation keeps the real deposit and rollover and the
real withdraw post-state; only the withdraw guard is weakened. Transfer is
omitted: the counterexample does not need it, as with the restricted
operation sets of the base refutation controls. -/
inductive StepNC : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNC st (.deposit d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      guardNoChain d st → StepNC st (.withdraw d) (d.post st)
  | rollover {st : St Toy} : StepNC st .rollover st.rollover

inductive RunNC : List (Tx Toy) → St Toy → Prop where
  | empty : RunNC [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNC txs st → StepNC st tx st' → RunNC (txs ++ [tx]) st'

noncomputable abbrev s2 : St Toy := dB.post st1
abbrev wEarly : WithdrawData Toy := ⟨(), note 5 0 0, (), 2⟩
noncomputable abbrev s3 : St Toy := (wEarly.post s2).rollover
abbrev wAgain : WithdrawData Toy := ⟨(), note 5 0 0, (), 2⟩

abbrev txs : List (Tx Toy) :=
  [.deposit d0, .deposit dB, .withdraw wEarly, .rollover, .withdraw wAgain]

theorem g1 : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128]

theorem g2 : dB.guard st1 := by
  norm_num [DepositData.guard, st1, DepositData.post, St.empty, St.leaves,
    Note.cm, Note.wf, LeanShieldedPool.Note.wf, U128, maxU128]
  decide

/-- The first spend also runs under the weakened guard (it satisfies the
real guard too; the real model rejects the SECOND spend, as in the
analogous "changed active nullifier" example in `Pool/Epoch.lean`). -/
theorem g3 : guardNoChain wEarly s2 := by
  norm_num [guardNoChain, st1, DepositData.post, St.empty,
    St.rootInWindow, St.inTreeAt, St.leaves, LeanShieldedPool.St.pushWindow,
    rootWindow, Note.ownedBy, LeanShieldedPool.Note.ownedBy, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128, Note.cm, Note.nfE,
    InsertionFacts, AppendFresh, bump]

/-- The frozen-history-free guard accepts the SECOND spend of the same
note after rollover. This part must elaborate. -/
theorem g4 : guardNoChain wAgain s3 := by
  norm_num [guardNoChain, WithdrawData.post, WithdrawData.nf, st1,
    DepositData.post, St.rollover, St.empty, St.rootInWindow, St.inTreeAt,
    St.leaves, LeanShieldedPool.St.pushWindow, rootWindow, Note.ownedBy,
    LeanShieldedPool.Note.ownedBy, Note.wf, LeanShieldedPool.Note.wf,
    U128, maxU128, Note.cm, Note.nfE, InsertionFacts, AppendFresh, bump, drop]

/-- The REAL withdraw guard rejects the same second spend: its `ChainFacts`
conjunct finds the epoch-0 nullifier of the note in the sealed epoch-0 list. -/
theorem real_guard_rejects : ¬ wAgain.guard s3 := by
  intro h
  have hmissing := h.2.2.2.1.1.2 0 (by decide) (by decide)
  exact hmissing (by decide)

/-- The weakened model ACCEPTS the cross-epoch double spend. -/
theorem accepted : ∃ st, RunNC txs st :=
  ⟨_, RunNC.step (RunNC.step (RunNC.step (RunNC.step (RunNC.step RunNC.empty
    (StepNC.deposit g1)) (StepNC.deposit g2)) (StepNC.withdraw g3))
    StepNC.rollover) (StepNC.withdraw g4)⟩

/-- The counterexample history satisfies the epoch `CryptoHyp`
(commitments differ in their salts; keys are a subsingleton), so the
failure below is due only to the dropped frozen-history check. -/
theorem txs_cryptoHyp : Candidates.CryptoHyp Toy txs := by
  constructor
  · intro n hn n' hn' hcm
    simp only [Candidates.runNotes, Candidates.notes, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd hcm (by decide)
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- `crossEpochNoDoubleSpend`, restated over the mutated model's runs, is
FALSE: the accepted history consumes (5, 0, 0), a note with value, twice.
The control passes only if this refutation builds. -/
theorem cross_epoch_double_spend_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNC txs st →
      Candidates.CryptoHyp Toy txs → Candidates.noteSpentAtMostOnce txs := by
  intro h
  obtain ⟨st, hr⟩ := accepted
  have hc := h txs st hr txs_cryptoHyp
  norm_num [Candidates.noteSpentAtMostOnce, Tx.valueConsumes, Note.cm,
    List.flatMap] at hc

end NegChainFacts
end LeanShieldedPool.Epoch
