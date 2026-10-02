-- Refutation control for `valueConservation_proof`. This file MUST BUILD.
-- The withdraw guard with the root-membership conjunct REMOVED accepts a
-- withdrawal of a note that was never deposited. On the accepted history
-- (deposit 5, ghost-withdraw 5) the conservation identity is FALSE:
-- deposited = 5 but withdrawn + live = 10. The history satisfies
-- `CryptoHyp`, so the final theorem proves the explicit negation of the
-- frozen Prop, restated over the mutated model's runs.
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

/-- The step relation with the membership-free withdraw. Deposit is the
real one; transfer is not needed for the counterexample. -/
inductive StepNM : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNM st (.deposit d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      guardNoMembership d st → StepNM st (.withdraw d) (d.post st)

inductive RunNM : List (Tx Toy) → St Toy → Prop where
  | empty : RunNM [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNM txs st → StepNM st tx st' → RunNM (txs ++ [tx]) st'

/-- A 5-unit note never deposited: salt 1, so its commitment (6) is not the
deposited note's commitment (5). -/
abbrev nGhost : Note Toy := ⟨(), 5, (), 1⟩
abbrev wGhost : WithdrawData Toy := ⟨(), nGhost, (), 1⟩

abbrev txs : List (Tx Toy) := [.deposit d0, .withdraw wGhost]

theorem g1 : d0.guard st0 := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

/-- After one real deposit, the membership-free guard accepts the ghost
withdrawal. -/
theorem g2 : guardNoMembership wGhost (d0.post st0) := by
  refine ⟨?_, rfl, ?_, by norm_num, ?_, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 5
    unfold U128 maxU128; norm_num
  · show (5:Nat) ≤ _
    norm_num [DepositData.post, St.empty, bump]

/-- The mutated model accepts the history. -/
theorem accepted : RunNM txs (wGhost.post (d0.post st0)) :=
  RunNM.step (RunNM.step RunNM.empty (StepNM.deposit g1)) (StepNM.withdraw g2)

/-- The history satisfies the conditional theorem's cryptographic
hypotheses (commitments 5 and 6 are distinct; keys are a subsingleton), so
the failure below is due only to the dropped guard. -/
theorem ghost_cryptoHyp : CryptoHyp Toy txs := by
  constructor
  · intro n hn m hm _ _ hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, nGhost] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- `valueConservation`, restated over the mutated model's runs, is FALSE:
on the accepted history it reads 5 = 5 + 5. The control passes only if this
refutation builds. -/
theorem conservation_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNM txs st → CryptoHyp Toy txs →
      ∀ t : Toy.Token, st.deposited t = st.withdrawn t + liveValue st t := by
  intro h
  have hc := h txs _ accepted ghost_cryptoHyp ()
  norm_num [WithdrawData.post, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump, drop] at hc

end NegConservation
end LeanShieldedPool
