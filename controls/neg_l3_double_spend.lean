-- EXPECT: unsolved goals
-- Negative control for `noDoubleSpend_proof`.
-- The withdraw post-state with ONLY the nullifier insertion REMOVED
-- (spentCms is still recorded) accepts a history that withdraws the same
-- note twice: freshness can never fail because no nullifier is recorded.
-- The accepted history consumes one commitment twice, so
-- `noteSpentAtMostOnce` is FALSE for it, and the history satisfies
-- `CryptoHyp` (proven below), so the failure is due only to the dropped
-- insertion. The proof attempt at the end must not close.
-- The dual single mutation (spentCms only) is neg_l3_spentcms.lean.
import LeanShieldedPool.Statements.L3
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegDoubleSpend

open NonVacuity

-- INSERTION REMOVED: no `nullifiers := ...`; spentCms is kept.
noncomputable def postNoInsert (d : WithdrawData Toy) (st : St Toy) : St Toy :=
  { st with
    spentCms := d.note.cm :: st.spentCms
    balance := drop st.balance d.note.token d.note.amount
    withdrawn := bump st.withdrawn d.note.token d.note.amount }

/-- The step relation with the insertion-free withdraw. Deposit is the real
one; transfer is not needed for the counterexample. -/
inductive StepNI : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNI st (.deposit d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepNI st (.withdraw d) (postNoInsert d st)

inductive RunNI : List (Tx Toy) → St Toy → Prop where
  | empty : RunNI [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNI txs st → StepNI st tx st' → RunNI (txs ++ [tx]) st'

/-- Second deposited note: salt 2, commitment 7, distinct from n0's (5).
It keeps the pool solvent for the second withdrawal of n0. -/
abbrev nB : Note Toy := ⟨(), 5, (), 2⟩
abbrev dB : DepositData Toy := ⟨nB, ()⟩
abbrev w : WithdrawData Toy := ⟨(), n0, (), 2⟩

abbrev txs : List (Tx Toy) :=
  [.deposit d0, .deposit dB, .withdraw w, .withdraw w]

noncomputable abbrev s1 := d0.post st0
noncomputable abbrev s2 := dB.post s1
noncomputable abbrev s3 := postNoInsert w s2

/-- The insertion-free model ACCEPTS the double withdrawal of n0. This part
must elaborate: the second freshness check passes because nothing was
recorded. -/
example : ∃ st, RunNI txs st := by
  have g1 : d0.guard st0 := by
    refine ⟨trivial, by norm_num, ?_, ?_⟩
    · show U128 5
      unfold U128 maxU128; norm_num
    · norm_num [St.empty, St.leaves]
  have g2 : dB.guard s1 := by
    refine ⟨trivial, by norm_num, ?_, ?_⟩
    · show U128 5
      unfold U128 maxU128; norm_num
    · norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
  have g3 : w.guard s2 := by
    refine ⟨?_, ?_, rfl, ?_, by norm_num, ?_, ?_⟩
    · show (2:Nat) ∈ _
      norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
    · show _ ∈ List.take 2 _
      norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
    · show _ ∉ _
      norm_num [DepositData.post, St.empty, St.fresh]
    · show U128 5
      unfold U128 maxU128; norm_num
    · show (5:Nat) ≤ _
      norm_num [DepositData.post, St.empty, bump]
  have g4 : w.guard s3 := by
    refine ⟨?_, ?_, rfl, ?_, by norm_num, ?_, ?_⟩
    · show (2:Nat) ∈ _
      norm_num [postNoInsert, DepositData.post, St.empty, St.pushWindow, rootWindow]
    · show _ ∈ List.take 2 _
      norm_num [postNoInsert, DepositData.post, St.empty, St.leaves, Note.cm]
    · show _ ∉ _
      norm_num [postNoInsert, DepositData.post, St.empty, St.fresh]
    · show U128 5
      unfold U128 maxU128; norm_num
    · show (5:Nat) ≤ _
      norm_num [postNoInsert, DepositData.post, St.empty, bump, drop]
  exact ⟨_, RunNI.step (RunNI.step (RunNI.step (RunNI.step RunNI.empty
    (StepNI.deposit g1)) (StepNI.deposit g2)) (StepNI.withdraw g3))
    (StepNI.withdraw g4)⟩

/-- The counterexample history satisfies the conditional theorem's
cryptographic hypotheses (commitments 5 and 7 are distinct; keys are a
subsingleton), so the failure below is due only to the dropped insertion.
This part must elaborate. -/
theorem txs_cryptoHyp : CryptoHyp Toy txs := by
  constructor
  · intro n hn m hm hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, nB] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- The accepted history consumes n0's commitment twice, so the frozen Prop
is FALSE for it. The control passes only if this proof fails. -/
example : noteSpentAtMostOnce txs := by
  norm_num [noteSpentAtMostOnce, spentCommitments, Tx.consumes, Note.cm,
    List.flatMap]

end NegDoubleSpend
end LeanShieldedPool
