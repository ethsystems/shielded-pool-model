-- Control (must compile): the transfer guard of the gated model asks that input 0 is a tree
-- member. An earlier guard let input 0 be ballast instead. After one deposit (leaf 9), the
-- transfer whose two inputs are ballast notes outside the tree satisfies every conjunct of the
-- earlier guard, and the model's guard rejects it. So the model accepts fewer histories, and an
-- earlier `CircuitFacts.t_member` (input 0 ballast or member) cannot supply the transfer case of
-- the refinement.
import Refinement.ProvenanceNonVacuity

namespace LeanShieldedPool.Refine.RefuteInput0

open LeanShieldedPool LeanShieldedPool.Refine

/-- The earlier transfer guard: input 0 may be ballast instead of a member. -/
def guardOld (d : TransferData Toy.P) (st : St Toy.P) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧
  d.in2.ownedBy d.key ∧
  (d.in1.isBallast ∨ st.inTreeAt d.snapshot d.in1.cm) ∧
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

/-- Ballast inputs (salts 10, 20; commitments 16, 26) and zero outputs (salts 30, 40;
commitments 36, 46), key 0, against the one-leaf snapshot. -/
def dB : TransferData Toy.P where
  key := (0 : Nat)
  in1 := ⟨(5 : Nat), 0, (0 : Nat), (10 : Nat)⟩
  in2 := ⟨(5 : Nat), 0, (0 : Nat), (20 : Nat)⟩
  out1 := ⟨(5 : Nat), 0, (0 : Nat), (30 : Nat)⟩
  out2 := ⟨(5 : Nat), 0, (0 : Nat), (40 : Nat)⟩
  snapshot := 1

/-- The earlier guard accepts `dB` after the deposit of note 9. -/
theorem old_accepts : guardOld dB ProvToy.st1 :=
  ⟨show (1 : Nat) ∈ ([1, 0] : List Nat) by decide, rfl, rfl, Or.inl rfl, Or.inl rfl,
    show dB.nf1 ∉ ([] : List Toy.P.Nullifier) from fun h => List.not_mem_nil h,
    show dB.nf2 ∉ ([] : List Toy.P.Nullifier) from fun h => List.not_mem_nil h,
    show (16 : Nat) ≠ 26 by decide, rfl, rfl, rfl,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl,
    show (36 : Nat) ∉ ([9] : List Nat) by decide, show (46 : Nat) ∉ ([9] : List Nat) by decide,
    show (36 : Nat) ≠ 46 by decide⟩

/-- The model's guard rejects `dB`: input 0 (commitment 16) is not in the tree `[9]`. -/
theorem new_rejects : ¬ dB.guard ProvToy.st1 := by
  intro hg
  have h : (16 : Nat) ∈ ([9] : List Nat).take 1 := hg.2.2.2.1
  exact absurd h (by decide)

/-- The refutation: the earlier guard does not imply the model's guard. -/
theorem old_guard_not_new : ∃ (d : TransferData Toy.P) (st : St Toy.P), guardOld d st ∧ ¬ d.guard st :=
  ⟨dB, ProvToy.st1, old_accepts, new_rejects⟩

end LeanShieldedPool.Refine.RefuteInput0

#print axioms LeanShieldedPool.Refine.RefuteInput0.old_guard_not_new
