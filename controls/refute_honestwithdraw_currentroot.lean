-- Refutation control for `honestWithdrawWindow_proof`. This file MUST BUILD.
-- The withdraw guard ALSO requires the proof's root to be the current
-- root: a contract whose `isKnownRoot` returns only
-- `root == commitmentRoot()` and never reads the window (the lookup at
-- ShieldedPool.sol:315 at pocs-private a04b8b3 removed). Every other
-- guard and every post-state is the real one. After two deposits the
-- window is [2, 1, 0]. The owner of the first note proves against the
-- older root 1, which is in the window and covers the note; the mutated
-- guard rejects it because 1 is not the current leaf count 2. The final
-- theorem proves the explicit negation of the frozen Prop, restated over
-- the mutated model's runs.
import LeanShieldedPool.Proofs.TierB

namespace LeanShieldedPool
namespace NegHonestWithdrawCurrentRoot

open NonVacuity OwnerKeyNonVacuity

-- MUTATION: withdrawals only against the current root.
def guardCur (d : WithdrawData Toy) (st : St Toy) : Prop :=
  d.guard st ∧ d.snapshot = st.leaves.length

/-- The step relation with the mutated withdraw guard. Every other guard
and every post-state is real. -/
inductive StepCR : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepCR st (.deposit d) (d.post st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      d.guard st → StepCR st (.transfer d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      guardCur d st → StepCR st (.withdraw d) (d.post st)

inductive RunCR : List (Tx Toy) → St Toy → Prop where
  | empty : RunCR [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunCR txs st → StepCR st tx st' → RunCR (txs ++ [tx]) st'

/-- A second 3-unit deposit; its commitment is 10. -/
abbrev d1 : DepositData Toy := ⟨⟨(), 3, (), 7⟩, ()⟩

theorem deposit1_guard : d1.guard (d0.post st0) := by
  norm_num [DepositData.guard, DepositData.post, St.empty, St.leaves, Note.cm,
    U128, maxU128]

noncomputable abbrev st2 : St Toy := d1.post (d0.post st0)

/-- The mutated model accepts both deposits, through the real guards. -/
theorem accepted : RunCR [.deposit d0, .deposit d1] st2 :=
  RunCR.step (RunCR.step RunCR.empty (StepCR.deposit deposit_guard))
    (StepCR.deposit deposit1_guard)

theorem window_eq : st2.window = [2, 1, 0] := rfl

/-- `honestWithdrawWindow`, restated over the mutated model's runs, is
FALSE: the owner of the first note meets every hypothesis at the window
root 1, but the mutated guard accepts only the current root 2. -/
theorem window_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunCR txs st →
      ∀ (k : Toy.SpendKey) (n : Note Toy) (r : Toy.Address) (s : Nat),
        s ∈ st.window → n ∈ st.minted.take s →
        n.ownedBy k → st.fresh (n.nf k) →
        n.amount ≠ 0 → n.amount ≤ st.balance n.token →
        ∃ st' : St Toy,
          StepCR st (.withdraw ⟨k, n, r, s⟩) st' ∧
          RunCR (txs ++ [.withdraw ⟨k, n, r, s⟩]) st' ∧
          st'.balance n.token + n.amount = st.balance n.token := by
  intro h
  have hwin : (1 : Nat) ∈ st2.window := by
    rw [window_eq]
    decide
  have hmem : n0 ∈ st2.minted.take 1 := List.mem_singleton.mpr rfl
  have hfresh : st2.fresh (n0.nf ()) := List.not_mem_nil
  have hbal : n0.amount ≤ st2.balance n0.token := by
    show 5 ≤ bump (bump (fun _ => 0) () 5) () 3 ()
    norm_num [bump]
  obtain ⟨st', hs, _, _⟩ :=
    h _ _ accepted () n0 () 1 hwin hmem rfl hfresh (by decide) hbal
  cases hs with
  | withdraw hg =>
      have hcur : (1 : Nat) = st2.leaves.length := hg.2
      have hl : st2.leaves.length = 2 := rfl
      rw [hl] at hcur
      exact absurd hcur (by decide)

end NegHonestWithdrawCurrentRoot
end LeanShieldedPool
