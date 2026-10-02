-- Refutation control for `noOverWithdrawal_proof`. This file MUST BUILD.
-- Same weakened withdraw guard as refute_l4_solvency (membership and
-- solvency conjuncts removed): after a 5-unit deposit and an accepted
-- 7-unit withdrawal, total withdrawn (7) exceeds total deposited (5). The
-- final theorem proves the explicit negation of the frozen Prop, restated
-- over the mutated model's runs.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4OverWithdrawal

open NonVacuity

-- GUARDS REMOVED: no `st.inTreeAt`, no `d.note.amount ≤ st.balance _`.
def guardNoSolvency (d : WithdrawData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.note.ownedBy d.key ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount

/-- The step relation with the weakened withdraw. Deposit is the real one;
transfer is not needed for the counterexample. -/
inductive StepNB : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNB st (.deposit d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      guardNoSolvency d st → StepNB st (.withdraw d) (d.post st)

inductive RunNB : List (Tx Toy) → St Toy → Prop where
  | empty : RunNB [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNB txs st → StepNB st tx st' → RunNB (txs ++ [tx]) st'

/-- A 7-unit note never deposited (commitment 16). -/
abbrev nBig : Note Toy := ⟨(), 7, (), 9⟩
abbrev wBig : WithdrawData Toy := ⟨(), nBig, (), 1⟩

abbrev txs : List (Tx Toy) := [.deposit d0, .withdraw wBig]

theorem deposit_guard : d0.guard st0 := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

/-- After one 5-unit deposit, the weakened guard accepts the 7-unit
withdrawal. -/
theorem withdraw_guard : guardNoSolvency wBig (d0.post st0) := by
  refine ⟨?_, rfl, ?_, by norm_num, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 7
    unfold U128 maxU128; norm_num

/-- The mutated model accepts the history. -/
theorem accepted : RunNB txs (wBig.post (d0.post st0)) :=
  RunNB.step (RunNB.step RunNB.empty (StepNB.deposit deposit_guard))
    (StepNB.withdraw withdraw_guard)

/-- `noOverWithdrawal`, restated over the mutated model's runs, is FALSE: on
the accepted history it reads 7 ≤ 5. The control passes only if this refutation builds. -/
theorem overwithdrawal_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNB txs st →
      ∀ t : Toy.Token, st.withdrawn t ≤ st.deposited t := by
  intro h
  have hc := h txs _ accepted ()
  norm_num [WithdrawData.post, DepositData.post, St.empty, bump, drop] at hc

end NegL4OverWithdrawal
end LeanShieldedPool
