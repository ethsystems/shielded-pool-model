-- Refutation control for `windowBoundary_proof` and
-- `noMidTransferRoot_proof`. This file MUST BUILD.
-- The transfer post-state ALSO records the root between its two inserts
-- (leaf count + 1): the intermediate-root bug that pocs-private#12 fixed.
-- Every guard is the real one. After one deposit and one transfer the
-- window is [3, 2, 1, 0]. Entry 2 is not an operation boundary: the
-- accepted prefixes of that history end at 1 and 3 leaves, and 2 is the
-- count between the transfer's two inserts. The final theorems prove the
-- explicit negations of the two frozen Props, restated over the mutated
-- model's runs, and show that the weak bound `s ≤ leaf count` still holds
-- on the same history.
import LeanShieldedPool.Proofs.TierB

namespace LeanShieldedPool
namespace NegWindowIntermediate

open NonVacuity OwnerKeyNonVacuity

-- MUTATION: one extra push of the intermediate root before the final one.
def postMid (d : TransferData Toy) (st : St Toy) : St Toy :=
  { d.post st with
    window := St.pushWindow (St.pushWindow st.window (st.minted.length + 1))
      (st.minted.length + 2) }

/-- The step relation with the mutated transfer post. All guards are real. -/
inductive StepMid : St Toy → Tx Toy → St Toy → Prop where
  | deposit {st : St Toy} {d : DepositData Toy} :
      d.guard st → StepMid st (.deposit d) (d.post st)
  | transfer {st : St Toy} {d : TransferData Toy} :
      d.guard st → StepMid st (.transfer d) (postMid d st)
  | withdraw {st : St Toy} {d : WithdrawData Toy} :
      d.guard st → StepMid st (.withdraw d) (d.post st)

inductive RunMid : List (Tx Toy) → St Toy → Prop where
  | empty : RunMid [] st0
  | step {txs : List (Tx Toy)} {st st' : St Toy} {tx : Tx Toy} :
      RunMid txs st → StepMid st tx st' → RunMid (txs ++ [tx]) st'

/-- Leaves inserted by each operation (Section 4). -/
def delta : Tx Toy → Nat
  | .deposit _ => 1
  | .transfer _ => 2
  | .withdraw _ => 0

theorem StepMid.leaves_length {st st' : St Toy} {tx : Tx Toy}
    (h : StepMid st tx st') : st'.leaves.length = st.leaves.length + delta tx := by
  cases h with
  | @deposit d hg =>
      show ((st.minted ++ [d.note]).map Note.cm).length = (st.minted.map Note.cm).length + 1
      rw [List.length_map, List.length_append, List.length_map]
      rfl
  | @transfer d hg =>
      show ((st.minted ++ [d.out1, d.out2]).map Note.cm).length =
        (st.minted.map Note.cm).length + 2
      rw [List.length_map, List.length_append, List.length_map]
      rfl
  | withdraw hg => rfl

theorem RunMid.leaves_length {txs : List (Tx Toy)} {st : St Toy}
    (h : RunMid txs st) : st.leaves.length = (txs.map delta).sum := by
  induction h with
  | empty => rfl
  | @step txs st st' tx hr hs ih =>
      rw [hs.leaves_length, ih, List.map_append, List.sum_append]
      rfl

abbrev txs : List (Tx Toy) := [.deposit d0, .transfer t0]
noncomputable abbrev stMid : St Toy := postMid t0 (d0.post st0)

/-- The mutated model accepts the history, through the real guards. -/
theorem accepted : RunMid txs stMid :=
  RunMid.step (RunMid.step RunMid.empty (StepMid.deposit deposit_guard))
    (StepMid.transfer transfer_guard)

theorem window_eq : stMid.window = [3, 2, 1, 0] := rfl

/-- Contrast: the real model accepts the same history (`transfer_run`) and
records only the boundaries 3, 1 and 0. -/
theorem real_window : (t0.post (d0.post st0)).window = [3, 1, 0] := rfl

/-- `windowBoundary`, restated over the mutated model's runs, is FALSE:
the window entry 2 is no prefix boundary. The control passes only if this
refutation builds. -/
theorem boundary_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunMid txs st → ∀ s ∈ st.window,
      s = 0 ∨
      ∃ (pre : List (Tx Toy)) (tx : Tx Toy) (st₀ st₁ : St Toy),
        pre ++ [tx] <+: txs ∧ RunMid pre st₀ ∧ StepMid st₀ tx st₁ ∧
        s = st₁.leaves.length := by
  intro h
  have h2 : (2 : Nat) ∈ stMid.window := by
    rw [window_eq]
    decide
  rcases h txs stMid accepted 2 h2 with h0 | ⟨pre, tx, st₀, st₁, hp, hr, hs, hlen⟩
  · exact absurd h0 (by decide)
  · have hsum := (RunMid.step hr hs).leaves_length
    have hle : (pre ++ [tx]).length ≤ 2 := hp.length_le
    have htake := List.prefix_iff_eq_take.mp hp
    rw [htake] at hsum
    have hl : (pre ++ [tx]).length = 1 ∨ (pre ++ [tx]).length = 2 := by
      rw [List.length_append, List.length_singleton] at hle ⊢
      omega
    rcases hl with hl | hl
    · rw [hl] at hsum
      rw [hsum] at hlen
      exact absurd hlen (by decide)
    · rw [hl] at hsum
      rw [hsum] at hlen
      exact absurd hlen (by decide)

/-- `noMidTransferRoot`, restated over the mutated model's runs, is FALSE:
the transfer follows a prefix that ends at 1 leaf, and 2 is in the
window. -/
theorem midroot_counterexample :
    ¬ ∀ (txs : List (Tx Toy)) (st : St Toy), RunMid txs st →
      ∀ (pre : List (Tx Toy)) (d : TransferData Toy) (st₀ : St Toy),
        pre ++ [.transfer d] <+: txs → RunMid pre st₀ →
        st₀.leaves.length + 1 ∉ st.window := by
  intro h
  have hpre : RunMid [.deposit d0] (d0.post st0) :=
    RunMid.step RunMid.empty (StepMid.deposit deposit_guard)
  have h2 : (d0.post st0).leaves.length + 1 ∈ stMid.window := by
    show (2 : Nat) ∈ stMid.window
    rw [window_eq]
    decide
  exact h txs stMid accepted [.deposit d0] t0 (d0.post st0) (List.prefix_refl _) hpre h2

/-- The weak bound misses the bug: on the same accepted history every
window entry is at most the leaf count. -/
theorem weak_holds : ∀ s ∈ stMid.window, s ≤ stMid.leaves.length := by
  rw [window_eq]
  decide

end NegWindowIntermediate
end LeanShieldedPool
