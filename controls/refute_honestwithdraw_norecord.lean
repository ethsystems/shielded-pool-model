-- Refutation control for `honestWithdraw_proof`. This file MUST BUILD.
-- The deposit post-state does NOT push its root into the window. Every
-- guard and every other post-state is the real one. After one 5-unit
-- deposit the window is still [0], so the honest owner's withdrawal
-- against the current root (1 leaf) has no accepted step. In the model
-- the current root is accepted only through the window, so the missing
-- push blocks it. The contract would still accept that withdrawal:
-- `isKnownRoot` accepts the current root before it reads the window
-- (ShieldedPool.sol:314 at pocs-private a04b8b3). This control checks the
-- model's push, not the contract. `refute_honestwithdraw_currentroot.lean`
-- checks old roots. The final theorem proves the explicit negation of the
-- frozen Prop, restated over the mutated model's runs.
import LeanShieldedPool.Proofs.TierB

namespace LeanShieldedPool
namespace NegHonestWithdrawNoRecord

open NonVacuity OwnerKeyNonVacuity

-- MUTATION: the deposit keeps the old window.
noncomputable def postNoRecord (d : DepositData Toy) (st : St Toy) : St Toy :=
  { d.post st with window := st.window }

/-- The step relation with the mutated deposit post. All guards are real. -/
inductive StepNR : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNR st (.deposit d) (postNoRecord d st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      d.guard st → StepNR st (.transfer d) (d.post st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepNR st (.withdraw d) (d.post st)

inductive RunNR : List (Tx Toy) → St Toy → Prop where
  | empty : RunNR [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNR txs st → StepNR st tx st' → RunNR (txs ++ [tx]) st'

noncomputable abbrev stNR : St Toy := postNoRecord d0 st0

/-- The mutated model accepts the deposit, through the real guard. -/
theorem accepted : RunNR [.deposit d0] stNR :=
  RunNR.step RunNR.empty (StepNR.deposit deposit_guard)

theorem window_eq : stNR.window = [0] := rfl

/-- `honestWithdraw`, restated over the mutated model's runs, is FALSE:
the owner of the deposited note meets every hypothesis, but the current
root is not in the window. The control passes only if this refutation
builds. -/
theorem honest_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNR txs st →
      ∀ (k : Toy.SpendKey) (n : Note Toy) (r : Toy.Address),
        n ∈ st.minted → n.ownedBy k → st.fresh (n.nf k) →
        n.amount ≠ 0 → n.amount ≤ st.balance n.token →
        ∃ st' : St Toy,
          StepNR st (.withdraw ⟨k, n, r, st.leaves.length⟩) st' ∧
          RunNR (txs ++ [.withdraw ⟨k, n, r, st.leaves.length⟩]) st' ∧
          st'.balance n.token + n.amount = st.balance n.token := by
  intro h
  have hmem : n0 ∈ stNR.minted := List.mem_singleton.mpr rfl
  have hfresh : stNR.fresh (n0.nf ()) := List.not_mem_nil
  have hbal : n0.amount ≤ stNR.balance n0.token := by
    show 5 ≤ bump (fun _ => 0) () 5 ()
    norm_num [bump]
  obtain ⟨st', hs, _, _⟩ :=
    h _ _ accepted () n0 () hmem rfl hfresh (by decide) hbal
  cases hs with
  | withdraw hg =>
      have hw : (1 : Nat) ∈ stNR.window := hg.1
      rw [window_eq] at hw
      exact absurd hw (by decide)

end NegHonestWithdrawNoRecord
end LeanShieldedPool
