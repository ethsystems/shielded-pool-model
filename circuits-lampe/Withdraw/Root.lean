import Merkle.Fold
import Withdraw.Nullifier

/-!
W2 as a plain equation over the complete extracted withdraw `main`, and an accepting execution
at every depth `1 .. 32` (the active hashing branch of the Merkle loop runs).

`bmr_fwd_w`: the extracted `binary_merkle_root<32>` with the `hash_2` reference returns
`merkleRoot hash2v leaf depth indices path` (`Merkle.Fold.bmr_fwd` with the width-3 forward
result `Poseidon.Hash2.hash_2_fwd`). `bmr_pinned_w`: with `wgood_bmr` and `Good.pin`, every accepting
derivation of that call has an outcome with this value.
-/

namespace Withdraw.Root
open Lampe Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2 Merkle.Fold

theorem bmr_fwd_w (st : State p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32) :
    Omni p Γw st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', merkleRoot hash2v leaf depth indices path)) :=
  bmr_fwd (32 : U 32) hash2v _ (mem1 Withdraw.Lookup.bmr_filter) (fun st a b => hash_2_fwd st a b)
    st leaf depth indices path

theorem bmr_pinned_w {st Q} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32)
    (h : Omni p Γw st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path]) Q) :
    ∃ st', Q (some (st', merkleRoot hash2v leaf depth indices path)) :=
  (wgood_bmr bn254_gt leaf depth indices path).pin (bmr_fwd_w st leaf depth indices path) h

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

/-- W2 (with W3-W5): in every accepting execution of the complete extracted withdraw `main`, with
`C = hash4 token amount (ownerKey spending_key) salt`, `proof_length ≤ 32` and the public
`commitment_root` is the Merkle fold of `C` with `hash2v` over `path` and `indices` up to
`proof_length`; the public nullifier is `hash2v C spending_key`. -/
theorem accepting_main_withdraw_root {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    proof_length ≤ 32 ∧
      commitment_root = merkleRoot hash2v
        (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) proof_length indices path ∧
      nullifier = hash2v (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt) spending_key := by
  obtain ⟨hn, hle, st₅, hroot⟩ := Withdraw.Nullifier.accepting_main_withdraw_rules nullifier token amount
    recipient commitment_root spending_key salt proof_length path indices accepts rejects_failure
  obtain ⟨st', st₆, heq⟩ := bmr_pinned_w _ _ _ _ hroot
  exact ⟨hle, (Prod.mk.inj (Option.some.inj heq)).2.symm, hn⟩

section
open Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem verify_fwd_w {st} (leaf : Fp p) (d : U 32) (hd : d ≤ 32)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32) :
    Omni p Γw st («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, merkleRoot hash2v leaf d indices path, d, indices, path])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.vmp_filter)
  dsimp only [«withdraw-0.0.0::verify_merkle_proof»]
  repeat' first
    | apply bind_value (uleq_true hd)
    | (apply bind_result (bmr_fwd_w _ _ _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (merkleRoot hash2v leaf d indices path =
    merkleRoot hash2v leaf d indices path)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)

/-- `Withdraw.Nullifier.main_from_fwd` at any depth `d`: the `verify_merkle_proof` call is a premise
with an abstract root `R` (discharged below by `verify_fwd_w`). -/
theorem main_from_fwd_d (st : State p) (o : Fp p) (H4 : Fp p → Fp p → Fp p → Fp p → Fp p)
    (H2 : Fp p → Fp p → Fp p) (R : Fp p) (d : U 32)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)
    (ho : ∀ st, Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![(0 : Fp p)])
      (fun r => ∃ st', r = some (st', o)))
    (h4 : ∀ st a b c d, Omni p Γw st («withdraw-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', H4 a b c d)))
    (h2 : ∀ st a b, Omni p Γw st («withdraw-0.0.0::poseidon2».call h![] h![a, b])
      (fun r => ∃ st', r = some (st', H2 a b)))
    (hv : ∀ st, Omni p Γw st («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![H4 0 0 o 0, R, d, indices, path]) (fun r => ∃ st', r = some (st', ()))) :
    Omni p Γw st («withdraw-0.0.0::main».call h![]
      h![H2 (H4 0 0 o 0) 0, (0 : Fp p), (0 : Fp p), (0 : Fp p), R, (0 : Fp p), (0 : Fp p),
        d, path, indices])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.main_filter)
  dsimp only [«withdraw-0.0.0::main»]
  repeat' first
    | apply bind_value (Exec.RangeRun.zero_range (mem3 Withdraw.Lookup.range_filter))
    | (apply bind_result (ho _); intro st')
    | (apply bind_result (h4 _ _ _ _ _); intro st')
    | (apply bind_result (hv _); intro st')
    | (apply bind_result (h2 _ _ _); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (H2 (H4 0 0 o 0) 0 = H2 (H4 0 0 o 0) 0)) == true) = true; simp)
  all_goals exact ⟨_, rfl⟩

/-- Accepting executions of the complete extracted withdraw `main` at EVERY depth `d ≤ 32`, for
every path and direction bits: amount, token, key and salt 0, `nullifier = N0`, and
`commitment_root` the Merkle fold of the zero note `C0`. For `d ≥ 1` the loop runs its active
branch (the hasher call) at the positions `0 .. d-1`. -/
theorem main_accepting_execution_depth (st : State p) (d : U 32) (hd : d ≤ 32)
    (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32) :
    Omni p Γw st («withdraw-0.0.0::main».call h![]
      h![Withdraw.Nullifier.N0, (0 : Fp p), (0 : Fp p), (0 : Fp p),
        merkleRoot hash2v Withdraw.Nullifier.C0 d indices path, (0 : Fp p), (0 : Fp p), d, path, indices])
      (fun r => ∃ st', r = some (st', ())) :=
  main_from_fwd_d st _ _ _ _ d path indices (fun st => poseidon1_fwd st 0) poseidon4_fwd poseidon2_fwd
    (fun _ => verify_fwd_w _ d hd path indices)
end

/-- The depth-3 root of the zero note with a zero path and all direction bits `false` (the
extracted Noir test `test_withdraw_valid` uses this path shape): three active levels. -/
theorem root_depth3_generic (h : Fp p → Fp p → Fp p) (leaf : Fp p) :
    merkleRoot h leaf (3 : U 32) (List.Vector.replicate 32 false)
      (List.Vector.replicate 32 (0 : Fp p)) = h (h (h leaf 0) 0) 0 := by
  rfl

theorem root_depth3 :
    merkleRoot hash2v Withdraw.Nullifier.C0 (3 : U 32) (List.Vector.replicate 32 false)
      (List.Vector.replicate 32 (0 : Fp p)) =
      hash2v (hash2v (hash2v Withdraw.Nullifier.C0 0) 0) 0 :=
  root_depth3_generic hash2v Withdraw.Nullifier.C0

/-- Positive-depth non-vacuity of W2: the premises of `accepting_main_withdraw_root` hold at an
accepting execution with `proof_length = 3`, and the W2 equation there says the public root is
three `hash2v` levels above the commitment. -/
theorem withdraw_root_nonvacuous (st : State p) :
    (3 : U 32) ≤ 32 ∧ 1 ≤ (3 : U 32) ∧
      merkleRoot hash2v Withdraw.Nullifier.C0 (3 : U 32) (List.Vector.replicate 32 false)
        (List.Vector.replicate 32 (0 : Fp p)) =
      hash2v (hash2v (hash2v Withdraw.Nullifier.C0 0) 0) 0 := by
  have h := accepting_main_withdraw_root Withdraw.Nullifier.N0 0 0 0
    (merkleRoot hash2v Withdraw.Nullifier.C0 (3 : U 32) (List.Vector.replicate 32 false)
      (List.Vector.replicate 32 (0 : Fp p))) 0 0 (3 : U 32)
    (List.Vector.replicate 32 0) (List.Vector.replicate 32 false)
    (main_accepting_execution_depth st 3 (by decide) _ _) (by rintro ⟨_, h⟩; cases h)
  exact ⟨h.1, by decide, root_depth3⟩

#print axioms bmr_fwd_w
#print axioms bmr_pinned_w
#print axioms accepting_main_withdraw_root
#print axioms verify_fwd_w
#print axioms main_from_fwd_d
#print axioms main_accepting_execution_depth
#print axioms root_depth3_generic
#print axioms root_depth3
#print axioms withdraw_root_nonvacuous
end Withdraw.Root
