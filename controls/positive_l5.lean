-- Positive control: the five L5 theorems instantiate on the concrete toy
-- epoch profile, and a concrete accepted run through deposit, transfer,
-- rollover and a later withdrawal satisfies the epoch `CryptoHyp`, so
-- `crossEpochNoDoubleSpend` and `chainKeyBinding` apply to a nonempty
-- accepted history that crosses a rollover. A no-rollover prefix witnesses
-- `baseCaseSoundness`'s antecedent. Must build.
import LeanShieldedPool.Proofs.Epoch
import LeanShieldedPool.Proofs.EpochBase

open LeanShieldedPool.Epoch

example : Candidates.crossEpochNoDoubleSpend Examples.Toy :=
  crossEpochNoDoubleSpend_proof _
example : Candidates.frozenRootImmutability Examples.Toy :=
  frozenRootImmutability_proof _
example : Candidates.canonicalAppend Examples.Toy :=
  canonicalAppend_proof _
example : Candidates.chainKeyBinding Examples.Toy :=
  chainKeyBinding_proof _
example : Candidates.baseCaseSoundness Examples.Toy :=
  baseCaseSoundness_proof _

namespace LeanShieldedPool.Epoch.PositiveL5

open Examples

/-- Withdraw the first transfer output in epoch 1, after the rollover. -/
abbrev wOut : WithdrawData Toy := ⟨(), note 3 2 0, (), 3⟩

abbrev txs : List (Tx Toy) :=
  [.deposit d0, .transfer t0, .rollover, .withdraw wOut]

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

/-- The sealed epoch-0 list holds the two transfer nullifiers; the output
note's epoch-0 nullifier is not among them, so its frozen history is clear. -/
theorem g3 : wOut.guard (t0.post st1).rollover := by
  norm_num [WithdrawData.guard, WithdrawData.nf, TransferData.post,
    TransferData.nullifiers, st1, DepositData.post, St.rollover, St.empty,
    St.rootInWindow, St.inTreeAt, St.leaves, LeanShieldedPool.St.pushWindow,
    rootWindow, Note.ownedBy, LeanShieldedPool.Note.ownedBy, Note.wf,
    LeanShieldedPool.Note.wf, U128, maxU128, Note.cm, Note.nfE, SpendGuard,
    ChainFacts, InsertionFacts, AppendFresh, bump]
  decide

/-- The accepted run: deposit, transfer, rollover, then an epoch-1 spend. -/
theorem epoch_run :
    Run (fun _ => True) txs (wOut.post (t0.post st1).rollover) :=
  Run.step (Run.step (Run.step (Run.step Run.empty
    (Step.deposit g1)) (Step.transfer g2)) Step.rollover)
    (Step.withdraw g3)

/-- The run satisfies the epoch `CryptoHyp`: distinct notes have distinct
commitments and its keys are a subsingleton. -/
theorem txs_cryptoHyp : Candidates.CryptoHyp Toy txs := by
  constructor
  · intro n hn n' hn' hcm
    simp only [Candidates.runNotes, Candidates.notes, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd hcm (by decide)
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- Rows 10 and 13 (`crossEpochNoDoubleSpend`, `chainKeyBinding`): a
nonempty accepted history that crosses a rollover satisfies the epoch
`CryptoHyp`. This does not witness `baseCaseSoundness`'s no-rollover
premise; the prefix below does. -/
example : ∃ (txs : List (Tx Toy)) (st : St Toy),
    Run (fun _ => True) txs st ∧ Candidates.CryptoHyp Toy txs ∧
    Tx.rollover ∈ txs :=
  ⟨txs, _, epoch_run, txs_cryptoHyp,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- The no-rollover prefix, for row 14 (`baseCaseSoundness`). -/
abbrev txsP : List (Tx Toy) := [.deposit d0, .transfer t0]

theorem prefix_run : Run (fun _ => True) txsP (t0.post st1) :=
  Run.step (Run.step Run.empty (Step.deposit g1)) (Step.transfer g2)

theorem prefix_cryptoHyp : Candidates.CryptoHyp Toy txsP := by
  constructor
  · intro n hn n' hn' hcm
    simp only [Candidates.runNotes, Candidates.notes, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd hcm (by decide)
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- Row 14's antecedent is satisfiable: a nonempty accepted run without
rollover, with its epoch `CryptoHyp`. -/
example : ∃ (txs : List (Tx Toy)) (st : St Toy),
    Run (fun _ => True) txs st ∧ Candidates.CryptoHyp Toy txs ∧
    (∀ tx ∈ txs, tx ≠ .rollover) ∧ txs ≠ [] := by
  refine ⟨txsP, _, prefix_run, prefix_cryptoHyp, ?_, by simp⟩
  intro tx ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> nofun

end LeanShieldedPool.Epoch.PositiveL5
