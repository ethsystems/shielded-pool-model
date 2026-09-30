-- EXPECT: unsolved goals
-- Negative control for `poolSolvency_proof`.
-- The withdraw guard with the membership AND solvency conjuncts REMOVED
-- (they jointly protect the balance) accepts a 7-unit withdrawal from a
-- pool holding 5. Truncated Nat subtraction floors the balance at 0 and
-- the solvency identity is FALSE: 0 + 7 = 5. The proof attempt below must
-- not close.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4Solvency

open NonVacuity

-- GUARDS REMOVED: no `st.inTreeAt`, no `d.note.amount ≤ st.balance _`.
def guardNoSolvency (d : WithdrawData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.note.ownedBy d.key ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount

/-- A 7-unit note never deposited (commitment 16). -/
abbrev nBig : Note Toy := ⟨(), 7, (), 9⟩
abbrev wBig : WithdrawData Toy := ⟨(), nBig, (), 1⟩

/-- After one 5-unit deposit, the weakened guard accepts the 7-unit
withdrawal. This part must elaborate. -/
example : guardNoSolvency wBig (d0.post st0) := by
  refine ⟨?_, rfl, ?_, by norm_num, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 7
    unfold U128 maxU128; norm_num

/-- The solvency identity after the over-withdrawal. FALSE: it reads
0 + 7 = 5. The control passes only if this proof fails. -/
example :
    (wBig.post (d0.post st0)).balance () + (wBig.post (d0.post st0)).withdrawn ()
      = (wBig.post (d0.post st0)).deposited () := by
  norm_num [WithdrawData.post, DepositData.post, St.empty, bump, drop]

end NegL4Solvency
end LeanShieldedPool
