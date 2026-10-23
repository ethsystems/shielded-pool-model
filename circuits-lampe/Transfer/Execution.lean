import Transfer.Rules
import Deposit.MainHashes

/-!
Non-vacuity. One accepting execution of the complete extracted transfer `main`: all
tokens, amounts and the spending key 0; input 0 at depth 0 (`commitment_root = C₀`); input 1 is
a ballast note (amount 0, salt 1) with `proof_length_1 = 33`, which the depth bound would reject
if the circuit checked it. It runs the extracted hash_1, hash_4 and hash_2 code, the u128 casts,
the `if`, value conservation and the token checks.
-/

namespace Transfer.Execution
open Lampe Determinism Transfer.HashGood Transfer.Forward Transfer.Rules

section
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem root_zero_depth32 {st} (leaf : Fp p)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)
    (hasher : FuncRef [.array .field 2] .field) :
    Omni p Γt st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![hasher, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', leaf)) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.bmr_filter)
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  repeat' first
    | exec_pure
    | (apply bind_ref; intro addr hfresh)
  apply bind_value (loop_noop32 _ _ _ ?_)
  · run_steps
    all_goals try first | rfl | exact () | trivial
    all_goals
      dsimp [mapToValHeapCondition, RefPath.get]
      exact ⟨_, rfl⟩
  · intro i
    repeat' first
      | apply bind_value (Merkle.ZeroDepth.lt_zero32 _)
      | exec_pure
      | apply Omni.iteFalse
      | apply Omni.skip
      | rfl

theorem verify_zero32 {st} (leaf : Fp p)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32) :
    Omni p Γt st («transfer-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.vmp_filter)
  dsimp only [«transfer-0.0.0::verify_merkle_proof»]
  repeat' first
    | (apply bind_result (root_zero_depth32 _ _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (leaf = leaf)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩

/-- `(0 : u128) as Field`. -/
abbrev z : Fp p := (((0 : U 128).toNat : ℕ) : Fp p)

/-- Composition with abstract hash values (the forward results are premises; discharged below). -/
theorem main_from_fwd (st : State p) (o : Fp p) (H4 : Fp p → Fp p → Fp p → Fp p → Fp p)
    (H2 : Fp p → Fp p → Fp p)
    (ho : ∀ st, Omni p Γt st («transfer-0.0.0::poseidon1».call h![] h![(0 : Fp p)])
      (fun r => ∃ st', r = some (st', o)))
    (h4 : ∀ st a b c d, Omni p Γt st («transfer-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', H4 a b c d)))
    (h2 : ∀ st a b, Omni p Γt st («transfer-0.0.0::poseidon2».call h![] h![a, b])
      (fun r => ∃ st', r = some (st', H2 a b))) :
    Omni p Γt st («transfer-0.0.0::main».call h![]
      h![H2 (H4 0 z o 0) 0, H2 (H4 0 z o 1) 0, H4 0 z 0 0, H4 0 z 0 0, H4 0 z o 0, (0 : Fp p),
        (0 : Fp p), (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p), (0 : U 128), (1 : Fp p),
        (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p),
        (0 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false,
        (33 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.main_filter)
  dsimp only [«transfer-0.0.0::main»]
  repeat' first
    | (apply bind_result (ho _); intro st')
    | (apply bind_result (h4 _ _ _ _ _); intro st')
    | (apply bind_result (verify_zero32 _ _ _); intro st')
    | (apply bind_result (h2 _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change Nat.le _ _; simp; done)
  all_goals try (simp only [beq_true, decide_eq_true_eq]; rfl)
  all_goals try (simp; done)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩
end

/-- Owner key, input commitments, nullifiers and output commitment of the execution. -/
abbrev K0 : Fp p := Deposit.Commitment.ownerKey 0
abbrev C0 : Fp p := Deposit.Commitment.hash4 0 z K0 0
abbrev C1 : Fp p := Deposit.Commitment.hash4 0 z K0 1
abbrev N0 : Fp p := Poseidon.Hash2.hash2v C0 0
abbrev N1 : Fp p := Poseidon.Hash2.hash2v C1 0
abbrev D0 : Fp p := Deposit.Commitment.hash4 0 z 0 0

/-- An accepting execution of the complete extracted transfer `main`. -/
theorem main_accepting_execution (st : State p) :
    Omni p Γt st («transfer-0.0.0::main».call h![]
      h![N0, N1, D0, D0, C0, (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : U 128), (0 : Fp p),
        (0 : Fp p), (0 : U 128), (1 : Fp p), (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p),
        (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p),
        (0 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false,
        (33 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false])
      (fun r => ∃ st', r = some (st', ())) :=
  main_from_fwd st _ _ _ (fun st => poseidon1_fwd st 0) poseidon4_fwd poseidon2_fwd

/-- The premises of `accepting_main_transfer_rules` are satisfiable: the execution above meets
them, the conclusions hold at it, and its ballast input has `proof_length_1 = 33 > 32`, so the
depth bound and the Merkle check do not apply to a zero-amount input 1. -/
theorem transfer_rules_nonvacuous (st : State p) :
    N0 = Poseidon.Hash2.hash2v C0 0 ∧ N1 = Poseidon.Hash2.hash2v C1 0 ∧ (0 : U 32) ≤ 32 ∧ ¬ ((33 : U 32) ≤ 32) := by
  have h := accepting_main_transfer_rules N0 N1 D0 D0 C0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 33
    (List.Vector.replicate 32 0) (List.Vector.replicate 32 0)
    (List.Vector.replicate 32 false) (List.Vector.replicate 32 false)
    (main_accepting_execution st) (by rintro ⟨_, h⟩; cases h)
  exact ⟨h.2.2.1, h.2.2.2.1, h.1.1, by decide⟩

#print axioms root_zero_depth32
#print axioms verify_zero32
#print axioms main_from_fwd
#print axioms main_accepting_execution
#print axioms transfer_rules_nonvacuous
end Transfer.Execution
