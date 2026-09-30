-- EXPECT: unsolved goals
-- Negative control for `valueConservation_proof`: the spentCms half of the
-- combined insertion mutation, tested alone. The withdraw post-state with
-- ONLY the spentCms insertion REMOVED (the nullifier is still recorded)
-- keeps double spends blocked, but the withdrawn note is never marked
-- spent, so it still counts as live: after deposit 5, withdraw 5, the
-- conservation identity reads 5 = 5 + 5. The proof attempt at the end
-- must not close.
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

/-- The real withdraw guard accepts n0's withdrawal after its deposit; the
mutation is only in the post-state. This part must elaborate. -/
theorem withdraw_guard : w0.guard (d0.post st0) := by
  norm_num [WithdrawData.guard, WithdrawData.nf, Note.nf, Note.cm, Note.ownedBy,
    St.rootInWindow, St.inTreeAt, St.fresh, St.leaves, St.empty, St.pushWindow,
    rootWindow, DepositData.post, U128, maxU128, bump]

/-- The counterexample history satisfies `CryptoHyp` (single note, keys a
subsingleton), so the failure below is due only to the dropped insertion.
This part must elaborate. -/
theorem txs_cryptoHyp : CryptoHyp Toy [.deposit d0, .withdraw w0] := by
  constructor
  · intro n hn m hm _
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;> rfl
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- The conservation identity after the bookkeeping-free withdrawal.
FALSE: it reads 5 = 5 + 5, because n0 still counts as live. The control
passes only if this proof fails. -/
example :
    (postNoSpentCms w0 (d0.post st0)).deposited ()
      = (postNoSpentCms w0 (d0.post st0)).withdrawn ()
        + liveValue (postNoSpentCms w0 (d0.post st0)) () := by
  norm_num [postNoSpentCms, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump, drop]

end NegSpentCms
end LeanShieldedPool
