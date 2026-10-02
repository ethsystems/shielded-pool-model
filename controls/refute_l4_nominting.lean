-- Refutation control for `noMinting_proof`. This file MUST BUILD.
-- The transfer guard with the FIRST-INPUT membership conjunct REMOVED
-- accepts a transfer that spends a 7-unit note never deposited, minting
-- its value into two live outputs. Live value (5 + 4 + 3 = 12) then
-- exceeds total deposits (5). The history satisfies `CryptoHyp`, so the
-- final theorem proves the explicit negation of the frozen Prop, restated
-- over the mutated model's runs.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4NoMinting

open NonVacuity

-- GUARD REMOVED: no `st.inTreeAt d.snapshot d.in1.cm`.
def guardNoMembership (d : TransferData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧
  d.in2.ownedBy d.key ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  st.fresh d.nf1 ∧
  st.fresh d.nf2 ∧
  d.nf1 ≠ d.nf2 ∧
  d.in2.token = d.in1.token ∧
  d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  U128 d.in1.amount ∧
  U128 d.in2.amount ∧
  U128 d.out1.amount ∧
  U128 d.out2.amount ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount ∧
  d.out1.cm ∉ st.leaves ∧
  d.out2.cm ∉ st.leaves ∧
  d.out1.cm ≠ d.out2.cm

/-- The step relation with the membership-free transfer. Deposit is the
real one; withdraw is not needed for the counterexample. -/
inductive StepNM : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepNM st (.deposit d) (d.post st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      guardNoMembership d st → StepNM st (.transfer d) (d.post st)

inductive RunNM : List (Tx Toy) → St Toy → Prop where
  | empty : RunNM [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunNM txs st → StepNM st tx st' → RunNM (txs ++ [tx]) st'

/-- A transfer spending a 7-unit note never deposited (commitment 16),
with a ballast second input, into 4 + 3 outputs. -/
abbrev tMint : TransferData Toy :=
  { key := ()
    in1 := ⟨(), 7, (), 9⟩
    in2 := ⟨(), 0, (), 1⟩
    out1 := ⟨(), 4, (), 11⟩
    out2 := ⟨(), 3, (), 20⟩
    snapshot := 1 }

abbrev txs : List (Tx Toy) := [.deposit d0, .transfer tMint]

theorem deposit_guard : d0.guard st0 := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

/-- After one 5-unit deposit, the weakened guard accepts the minting
transfer. -/
theorem transfer_guard : guardNoMembership tMint (d0.post st0) := by
  refine ⟨?_, rfl, rfl, Or.inl rfl, ?_, ?_, by norm_num [TransferData.nf1,
      TransferData.nf2, Note.nf, Note.cm], rfl, rfl, rfl, ?_, ?_, ?_, ?_,
      by norm_num, ?_, ?_, by norm_num [Note.cm]⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 7
    unfold U128 maxU128; norm_num
  · show U128 0
    unfold U128 maxU128; norm_num
  · show U128 4
    unfold U128 maxU128; norm_num
  · show U128 3
    unfold U128 maxU128; norm_num
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]

/-- The mutated model accepts the history. -/
theorem accepted : RunNM txs (tMint.post (d0.post st0)) :=
  RunNM.step (RunNM.step RunNM.empty (StepNM.deposit deposit_guard))
    (StepNM.transfer transfer_guard)

/-- The history satisfies `CryptoHyp`: its five notes have the distinct
commitments 5, 16, 1, 15 and 23, and keys are a subsingleton. The failure
below is due only to the dropped guard. -/
theorem txs_cryptoHyp : CryptoHyp Toy txs := by
  constructor
  · intro n hn m hm _ _ hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, tMint] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- `noMinting`, restated over the mutated model's runs, is FALSE: on the
accepted history it reads 12 ≤ 5. The control passes only if this refutation builds. -/
theorem minting_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunNM txs st → CryptoHyp Toy txs →
      ∀ t : Toy.Token, liveValue st t ≤ st.deposited t := by
  intro h
  have hc := h txs _ accepted txs_cryptoHyp ()
  norm_num [TransferData.post, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump] at hc

end NegL4NoMinting
end LeanShieldedPool
