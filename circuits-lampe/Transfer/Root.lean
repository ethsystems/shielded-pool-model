import Merkle.Fold
import Transfer.Rules

/-!
T3 as plain equations over the complete extracted transfer `main`. `bmr_fwd_t` is
`Merkle.Fold.bmr_fwd` in the transfer environment with the forward result `Transfer.Forward.hash_2_fwd`;
`bmr_pinned_t` pins it with `tgood_bmr` and `Good.pin`.
-/

namespace Transfer.Root
open Lampe Determinism Transfer.HashGood Transfer.Forward Merkle.Fold Poseidon.Hash2

theorem bmr_fwd_t (st : State p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32) :
    Omni p Γt st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', merkleRoot hash2v leaf depth indices path)) :=
  bmr_fwd (32 : U 32) hash2v _ (Withdraw.Rules.mem1 Transfer.Lookup.bmr_filter) (fun st a b => hash_2_fwd st a b)
    st leaf depth indices path

theorem bmr_pinned_t {st Q} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32)
    (h : Omni p Γt st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path]) Q) :
    ∃ st', Q (some (st', merkleRoot hash2v leaf depth indices path)) :=
  (tgood_bmr Withdraw.Rules.bn254_gt leaf depth indices path).pin (bmr_fwd_t st leaf depth indices path) h

/-- From a relational root (some derivation of the extracted root call returns `root`) to the
equation `root = merkleRoot ...`. -/
theorem root_eq {st root} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32)
    (h : Omni p Γt st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', root))) :
    root = merkleRoot hash2v leaf depth indices path := by
  obtain ⟨st', st₆, heq⟩ := bmr_pinned_t _ _ _ _ h
  exact (Prod.mk.inj (Option.some.inj heq)).2.symm

variable (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
  spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
  token_out_1 owner_out_1 salt_out_1 : Fp p)
variable (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
variable (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32)

/-- T3 (with T2, T4, T10) on the complete extracted transfer `main`. In every accepting
execution, with `Cᵢ = hash4 token_in_i amount_in_i (ownerKey spending_key) salt_in_i`:
input 0 has `proof_length_0 ≤ 32` and `commitment_root` is the Merkle fold of `C₀`; input 1 has
the same when `amount_in_1 ≠ 0` (for the ballast input nothing is claimed about its root). -/
theorem accepting_main_transfer_root {st Q}
    (accepts : Omni p Γt st
      («transfer-0.0.0::main».call h![]
        h![nullifier_0, nullifier_1, commitment_out_0, commitment_out_1, commitment_root,
          payload_hash, spending_key, token_in_0, amount_in_0, salt_in_0, token_in_1, amount_in_1,
          salt_in_1, token_out_0, amount_out_0, owner_out_0, salt_out_0, token_out_1, amount_out_1,
          owner_out_1, salt_out_1, proof_length_0, path_0, indices_0, proof_length_1, path_1,
          indices_1]) Q)
    (rejects_failure : ¬ Q none) :
    (proof_length_0 ≤ 32 ∧ commitment_root = merkleRoot hash2v
      (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
        (Deposit.Commitment.ownerKey spending_key) salt_in_0) proof_length_0 indices_0 path_0) ∧
    (amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧ commitment_root = merkleRoot hash2v
      (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
        (Deposit.Commitment.ownerKey spending_key) salt_in_1) proof_length_1 indices_1 path_1) ∧
    nullifier_0 = hash2v (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_0) spending_key ∧
    nullifier_1 = hash2v (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
      (Deposit.Commitment.ownerKey spending_key) salt_in_1) spending_key ∧
    commitment_out_0 = Deposit.Commitment.hash4 token_out_0 ((amount_out_0.toNat : ℕ) : Fp p) owner_out_0 salt_out_0 ∧
    commitment_out_1 = Deposit.Commitment.hash4 token_out_1 ((amount_out_1.toNat : ℕ) : Fp p) owner_out_1 salt_out_1 := by
  obtain ⟨⟨hle0, st₀, hr0⟩, h1, hn0, hn1, ho0, ho1⟩ := Transfer.Rules.accepting_main_transfer_rules
    nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
    spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
    token_out_1 owner_out_1 salt_out_1 amount_in_0 amount_in_1 amount_out_0 amount_out_1
    proof_length_0 proof_length_1 path_0 path_1 indices_0 indices_1 accepts rejects_failure
  refine ⟨⟨hle0, root_eq _ _ _ _ hr0⟩, ?_, hn0, hn1, ho0, ho1⟩
  intro hne
  obtain ⟨hle1, st₁, hr1⟩ := h1 hne
  exact ⟨hle1, root_eq _ _ _ _ hr1⟩

#print axioms bmr_fwd_t
#print axioms bmr_pinned_t
#print axioms root_eq
#print axioms accepting_main_transfer_root
end Transfer.Root
