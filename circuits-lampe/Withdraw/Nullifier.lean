import Poseidon.Hash2
import Deposit.MainHashes

/-!
W4 (the nullifier) as a plain equation, and non-vacuity of the withdraw rules.
`hash2v a b` is the value of the extracted `hash_2([a, b])` (width-3 forward function,
`Poseidon.Hash2.hash_2_fwd`). No claim about Poseidon's cryptographic properties.
-/

namespace Withdraw.Nullifier
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2

/-- Every derivation of the extracted withdraw `poseidon2(a, b)` has an outcome with value
`hash2v a b`. -/
theorem poseidon2_pinned {st Q} (a b : Fp p)
    (h : Omni p Γw st («withdraw-0.0.0::poseidon2».call h![] h![a, b]) Q) :
    ∃ st', Q (some (st', hash2v a b)) :=
  (wgood_poseidon2 bn254_gt a b).pin (poseidon2_fwd st a b) h

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

/-- W2-W5 on the complete extracted withdraw `main`: in every accepting execution, with the note
commitment `C = hash4 token amount (ownerKey spending_key) salt` (W3, W5: PUBLIC token and amount),
the public nullifier is `hash2v C spending_key` (W4), `proof_length ≤ 32`, and the extracted
`binary_merkle_root(hash_2, C, proof_length, indices, path)` returns `commitment_root` (W2). -/
theorem accepting_main_withdraw_rules {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    nullifier = hash2v (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) spending_key ∧
      proof_length ≤ 32 ∧
      ∃ st₅, Omni p Γw st₅
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt,
            proof_length, indices, path])
        (fun r => ∃ st₆, r = some (st₆, commitment_root)) := by
  obtain ⟨st₄, hle, hroot, hv⟩ := accepting_main_rules_eq nullifier token amount recipient
    commitment_root spending_key salt proof_length path indices accepts rejects_failure
  obtain ⟨r, hr, -⟩ := (wgood_vmp bn254_gt _ _ _ _ _).inter st₄ _ _ hv hv
  obtain ⟨st₇, u, -, h7⟩ := hr
  obtain ⟨_, st₈, heq⟩ := poseidon2_pinned _ _ h7
  exact ⟨(Prod.mk.inj (Option.some.inj heq)).2.symm, hle, hroot⟩

/-- The nullifier equation alone (W4). -/
theorem accepting_main_nullifier_eq {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    nullifier = hash2v (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) spending_key :=
  (accepting_main_withdraw_rules nullifier token amount recipient commitment_root spending_key salt
    proof_length path indices accepts rejects_failure).1

/-! ## Non-vacuity: one accepting execution of the complete extracted withdraw `main` -/

section
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem root_zero_depth32 {st} (leaf : Fp p)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)
    (hasher : FuncRef [.array .field 2] .field) :
    Omni p Γw st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![hasher, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', leaf)) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.bmr_filter)
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
    Omni p Γw st («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.vmp_filter)
  dsimp only [«withdraw-0.0.0::verify_merkle_proof»]
  repeat' first
    | (apply bind_result (root_zero_depth32 _ _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (leaf = leaf)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩

/-- The zero note: commitment and nullifier of the all-zero inputs. -/
abbrev C0 : Fp p := Deposit.Commitment.hash4 0 0 (Deposit.Commitment.ownerKey 0) 0
abbrev N0 : Fp p := hash2v C0 0

/-- Composition with abstract hash values (the forward results are premises here; they are
discharged below). Keeping the values abstract stops the tactics from unfolding the permutations. -/
theorem main_from_fwd (st : State p) (o : Fp p) (H4 : Fp p → Fp p → Fp p → Fp p → Fp p)
    (H2 : Fp p → Fp p → Fp p)
    (ho : ∀ st, Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![(0 : Fp p)])
      (fun r => ∃ st', r = some (st', o)))
    (h4 : ∀ st a b c d, Omni p Γw st («withdraw-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', H4 a b c d)))
    (h2 : ∀ st a b, Omni p Γw st («withdraw-0.0.0::poseidon2».call h![] h![a, b])
      (fun r => ∃ st', r = some (st', H2 a b))) :
    Omni p Γw st («withdraw-0.0.0::main».call h![]
      h![H2 (H4 0 0 o 0) 0, (0 : Fp p), (0 : Fp p), (0 : Fp p), H4 0 0 o 0, (0 : Fp p), (0 : Fp p),
        (0 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.main_filter)
  dsimp only [«withdraw-0.0.0::main»]
  repeat' first
    | apply bind_value (Exec.RangeRun.zero_range (mem3 Withdraw.Lookup.range_filter))
    | (apply bind_result (ho _); intro st')
    | (apply bind_result (h4 _ _ _ _ _); intro st')
    | (apply bind_result (verify_zero32 _ _ _); intro st')
    | (apply bind_result (h2 _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (H2 (H4 0 0 o 0) 0 = H2 (H4 0 0 o 0) 0)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩

/-- An accepting execution of the complete extracted withdraw `main` (amount 0, depth 0,
`commitment_root = C0`, `nullifier = N0`). It runs the extracted hash_1, hash_4 and hash_2 code. -/
theorem main_accepting_execution (st : State p) :
    Omni p Γw st («withdraw-0.0.0::main».call h![]
      h![N0, (0 : Fp p), (0 : Fp p), (0 : Fp p), C0, (0 : Fp p), (0 : Fp p), (0 : U 32),
        List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false])
      (fun r => ∃ st', r = some (st', ())) :=
  main_from_fwd st _ _ _ (fun st => poseidon1_fwd st 0) poseidon4_fwd poseidon2_fwd
end

/-- The premises of the withdraw rule theorems are satisfiable: the accepting execution above
meets them, and the conclusions hold at it. -/
theorem withdraw_rules_nonvacuous (st : State p) :
    N0 = hash2v (Deposit.Commitment.hash4 0 0 (Deposit.Commitment.ownerKey 0) 0) 0 ∧ (0 : U 32) ≤ 32 :=
  let h := accepting_main_withdraw_rules N0 0 0 0 C0 0 0 0
    (List.Vector.replicate 32 0) (List.Vector.replicate 32 false)
    (main_accepting_execution st) (by rintro ⟨_, h⟩; cases h)
  ⟨h.1, h.2.1⟩

#print axioms poseidon2_pinned
#print axioms accepting_main_withdraw_rules
#print axioms accepting_main_nullifier_eq
#print axioms root_zero_depth32
#print axioms verify_zero32
#print axioms main_from_fwd
#print axioms main_accepting_execution
#print axioms withdraw_rules_nonvacuous
end Withdraw.Nullifier
