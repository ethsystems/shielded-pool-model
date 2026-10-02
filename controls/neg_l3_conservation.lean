-- EXPECT: unsolved goals
-- Negative control for `valueConservation_proof`.
-- The withdraw guard with the root-membership conjunct REMOVED accepts a
-- withdrawal of a note that was never deposited. The conservation identity
-- is then FALSE on a concrete two-step history (deposit 5, ghost-withdraw
-- 5): deposited = 5 but withdrawn + live = 10. The proof attempt below must
-- not close.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegConservation

open NonVacuity

-- GUARD REMOVED: no `st.inTreeAt d.snapshot d.note.cm`.
def guardNoMembership (d : WithdrawData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.note.ownedBy d.key ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount ∧
  d.note.amount ≤ st.balance d.note.token

/-- A 5-unit note never deposited: salt 1, so its commitment (6) is not the
deposited note's commitment (5). -/
abbrev nGhost : Note Toy := ⟨(), 5, (), 1⟩
abbrev wGhost : WithdrawData Toy := ⟨(), nGhost, (), 1⟩

/-- After one real deposit, the membership-free guard accepts the ghost
withdrawal. This part must elaborate: the weakened guard really fires. -/
example : guardNoMembership wGhost (d0.post st0) := by
  refine ⟨?_, rfl, ?_, by norm_num, ?_, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 5
    unfold U128 maxU128; norm_num
  · show (5:Nat) ≤ _
    norm_num [DepositData.post, St.empty, bump]

/-- The counterexample history satisfies the conditional theorem's
cryptographic hypotheses (commitments 5 and 6 are distinct; keys are a
subsingleton), so the failure below is due only to the dropped guard.
This part must elaborate. -/
theorem ghost_cryptoHyp : CryptoHyp Toy [.deposit d0, .withdraw wGhost] := by
  constructor
  · intro n hn m hm _ _ hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, nGhost] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- The conservation identity after the ghost withdrawal. FALSE: it reads
5 = 5 + 5. The control passes only if this proof fails. -/
example :
    (wGhost.post (d0.post st0)).deposited ()
      = (wGhost.post (d0.post st0)).withdrawn ()
        + liveValue (wGhost.post (d0.post st0)) () := by
  norm_num [WithdrawData.post, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump, drop]

end NegConservation
end LeanShieldedPool
