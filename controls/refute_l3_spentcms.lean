-- Refutation control for `valueConservation_proof`: the spentCms half of
-- the combined insertion mutation, tested alone. This file MUST BUILD.
-- The withdraw post-state with ONLY the spentCms insertion REMOVED (the
-- nullifier is still recorded) keeps double spends blocked, but the
-- withdrawn note is never marked spent, so it still counts as live: after
-- deposit 5, withdraw 5, the conservation identity reads 5 = 5 + 5. The
-- history satisfies `CryptoHyp`, so the final theorem proves the explicit
-- negation of the frozen Prop, restated over the mutated model's runs.
import LeanShieldedPool.Statements.L3
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegSpentCms

open NonVacuity

-- INSERTION REMOVED: no `spentCms := ...`; the nullifier is kept.
noncomputable def postNoSpentCms (d : WithdrawData Toy) (st : St Toy) : St Toy :=
  { st with
    nullifiers := d.nf :: st.nullifiers
    balance := drop st.balance d.note.token d.note.amount
    withdrawn := bump st.withdrawn d.note.token d.note.amount }

/-- The step relation with the bookkeeping-free withdraw. Deposit is the
real one; transfer is not needed for the counterexample. -/
inductive StepNS : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNS st (.deposit d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepNS st (.withdraw d) (postNoSpentCms d st)

inductive RunNS : List (Tx Toy) → St Toy → Prop where
  | empty : RunNS [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNS txs st → StepNS st tx st' → RunNS (txs ++ [tx]) st'

abbrev txs : List (Tx Toy) := [.deposit d0, .withdraw w0]

theorem deposit_guard : d0.guard st0 := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

/-- The real withdraw guard accepts n0's withdrawal after its deposit; the
mutation is only in the post-state. -/
theorem withdraw_guard : w0.guard (d0.post st0) := by
  norm_num [WithdrawData.guard, WithdrawData.nf, Note.nf, Note.cm, Note.ownedBy,
    St.rootInWindow, St.inTreeAt, St.fresh, St.leaves, St.empty, St.pushWindow,
    rootWindow, DepositData.post, U128, maxU128, bump]

/-- The mutated model accepts the history. -/
theorem accepted : RunNS txs (postNoSpentCms w0 (d0.post st0)) :=
  RunNS.step (RunNS.step RunNS.empty (StepNS.deposit deposit_guard))
    (StepNS.withdraw withdraw_guard)

/-- The history satisfies `CryptoHyp` (single note, keys a subsingleton),
so the failure below is due only to the dropped insertion. -/
theorem txs_cryptoHyp : CryptoHyp Toy txs := by
  constructor
  · intro n hn m hm _ _ _
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;> rfl
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- `valueConservation`, restated over the mutated model's runs, is FALSE:
on the accepted history it reads 5 = 5 + 5, because n0 still counts as
live. The control passes only if this refutation builds. -/
theorem conservation_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNS txs st → CryptoHyp Toy txs →
      ∀ t : Toy.Token, st.deposited t = st.withdrawn t + liveValue st t := by
  intro h
  have hc := h txs _ accepted txs_cryptoHyp ()
  norm_num [postNoSpentCms, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump, drop] at hc

end NegSpentCms
end LeanShieldedPool
