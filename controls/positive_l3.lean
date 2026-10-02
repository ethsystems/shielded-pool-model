-- Positive control: the three L3 theorems instantiate on the concrete toy
-- PrimSpec. Must build.
import LeanShieldedPool.Proofs.NoDoubleSpend
import LeanShieldedPool.Proofs.Conservation
import LeanShieldedPool.Proofs.EventReplay
import LeanShieldedPool.Draft.NonVacuity

open LeanShieldedPool

example : noDoubleSpend NonVacuity.Toy := noDoubleSpend_proof _
example : valueConservation NonVacuity.Toy := valueConservation_proof _
example : nullifierUniqueness NonVacuity.Toy := nullifierUniqueness_proof _

open LeanShieldedPool.NonVacuity LeanShieldedPool.EventLogNonVacuity

/-- The deposit-transfer-withdraw toy run satisfies CryptoHyp, so the
conditional theorems apply to at least one accepted history. -/
theorem toy_run_cryptoHyp : CryptoHyp Toy [.deposit d0, .transfer t0, .withdraw w1] := by
  constructor
  · intro n hn m hm _ _ hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, t0, w1] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- The hypotheses of the conditional theorems are jointly satisfiable. -/
example : ∃ txs st, Run (fun _ => True) txs st ∧ CryptoHyp Toy txs ∧
    (Tx.transfer t0) ∈ txs :=
  ⟨_, _, all_operations_run, toy_run_cryptoHyp,
    List.mem_cons_of_mem _ List.mem_cons_self⟩
