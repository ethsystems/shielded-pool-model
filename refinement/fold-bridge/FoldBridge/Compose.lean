import FoldBridge.Bridge
import Withdraw.Root
import Transfer.Root
import Transfer.Execution

/-!
# W2 and T3 composed with the LeanIMT binding through the field bridge

`Withdraw.Root.accepting_main_withdraw_root` and `Transfer.Root.accepting_main_transfer_root` give the
circuit equation `commitment_root = merkleRoot hash2v C proof_length indices path`. With
`FoldBridge.binding_eq` this becomes: if the value of the public `commitment_root` is the contract
root `rootOf (Hn hash2v) L`, then `C.val ∈ L` or `LeanImt.Bad` holds for the witness path.
`withdraw_tree_nonvacuous` (every depth) and `transfer_tree_nonvacuous` (depth 0) show that the
premises are satisfiable by accepting executions.
-/

namespace FoldBridge
open Lampe LeanShieldedPool.Refine LeanShieldedPool.Refine.LeanImt

/-! ## W2 and T3 composed with the binding -/

section W2
open Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2

/-- **W2 composed with A9a.** In every accepting execution of the complete extracted withdraw
`main` whose public `commitment_root` has the contract root of `L` as its value, the note
commitment `C` (if nonzero) is a leaf of `L`, or `LeanImt.Bad` holds for the witness path. -/
theorem withdraw_member_or_bad (L : List ℕ)
    (nullifier token amount recipient commitment_root spending_key salt : Fp p)
    (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32) {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none)
    (hroot : commitment_root.val = rootOf (Hn hash2v) L)
    (hne : Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt ≠ 0) :
    (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt).val ∈ L ∨
      Bad (Hn hash2v) (imtOf (Hn hash2v) L).depth L
        (Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt).val
        (activePath proof_length.toNat indices.toList (path.map (·.val)).toList 32) := by
  obtain ⟨-, heq, -⟩ := Withdraw.Root.accepting_main_withdraw_root nullifier token amount recipient
    commitment_root spending_key salt proof_length path indices accepts rejects_failure
  exact binding_eq hash2v L commitment_root _ proof_length indices path hne heq hroot

end W2

section T3
open Determinism Transfer.HashGood Transfer.Forward Poseidon.Hash2

/-- **T3 composed with A9a.** In every accepting execution of the complete extracted transfer
`main` whose public `commitment_root` has the contract root of `L` as its value: input 0's
commitment (if nonzero) is a leaf of `L` or `Bad` holds for its path; the same for input 1 when
`amount_in_1 ≠ 0`. -/
theorem transfer_member_or_bad (L : List ℕ)
    (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
      spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
      token_out_1 owner_out_1 salt_out_1 : Fp p)
    (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
    (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32) {st Q}
    (accepts : Omni p Γt st
      («transfer-0.0.0::main».call h![]
        h![nullifier_0, nullifier_1, commitment_out_0, commitment_out_1, commitment_root,
          payload_hash, spending_key, token_in_0, amount_in_0, salt_in_0, token_in_1, amount_in_1,
          salt_in_1, token_out_0, amount_out_0, owner_out_0, salt_out_0, token_out_1, amount_out_1,
          owner_out_1, salt_out_1, proof_length_0, path_0, indices_0, proof_length_1, path_1,
          indices_1]) Q)
    (rejects_failure : ¬ Q none)
    (hroot : commitment_root.val = rootOf (Hn hash2v) L) :
    (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
        (Deposit.Commitment.ownerKey spending_key) salt_in_0 ≠ 0 →
      (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
          (Deposit.Commitment.ownerKey spending_key) salt_in_0).val ∈ L ∨
        Bad (Hn hash2v) (imtOf (Hn hash2v) L).depth L
          (Deposit.Commitment.hash4 token_in_0 ((amount_in_0.toNat : ℕ) : Fp p)
            (Deposit.Commitment.ownerKey spending_key) salt_in_0).val
          (activePath proof_length_0.toNat indices_0.toList (path_0.map (·.val)).toList 32)) ∧
    (amount_in_1 ≠ 0 →
      Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
          (Deposit.Commitment.ownerKey spending_key) salt_in_1 ≠ 0 →
      (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
          (Deposit.Commitment.ownerKey spending_key) salt_in_1).val ∈ L ∨
        Bad (Hn hash2v) (imtOf (Hn hash2v) L).depth L
          (Deposit.Commitment.hash4 token_in_1 ((amount_in_1.toNat : ℕ) : Fp p)
            (Deposit.Commitment.ownerKey spending_key) salt_in_1).val
          (activePath proof_length_1.toNat indices_1.toList (path_1.map (·.val)).toList 32)) := by
  obtain ⟨⟨-, h0⟩, h1, -⟩ := Transfer.Root.accepting_main_transfer_root nullifier_0 nullifier_1
    commitment_out_0 commitment_out_1 commitment_root payload_hash spending_key token_in_0
    salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0 token_out_1 owner_out_1
    salt_out_1 amount_in_0 amount_in_1 amount_out_0 amount_out_1 proof_length_0 proof_length_1
    path_0 path_1 indices_0 indices_1 accepts rejects_failure
  refine ⟨fun hne => binding_eq hash2v L commitment_root _ proof_length_0 indices_0 path_0 hne h0
    hroot, fun ha hne => ?_⟩
  obtain ⟨-, h1⟩ := h1 ha
  exact binding_eq hash2v L commitment_root _ proof_length_1 indices_1 path_1 hne h1 hroot

end T3

section Toy
open Determinism Withdraw.HashGood Withdraw.Rules Poseidon.Hash2

/-- **Non-vacuity of the W2 composition at every depth.** For every contract tree of at most
`2 ^ 32` leaves that contains the zero note `C0 = hash4 0 0 (ownerKey 0) 0`, the complete extracted
withdraw `main` has an accepting execution whose public `commitment_root` has the contract root
as its value: the premises of `withdraw_member_or_bad` hold. The witness is the LeanIMT compressed proof
(`complete_field`), run through the execution theorem of `circuits-lampe/`. -/
theorem withdraw_tree_nonvacuous (st : State p) (L : List ℕ) (hN : L.length ≤ 2 ^ 32)
    (hm : Withdraw.Nullifier.C0.val ∈ L) :
    ∃ (d : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32),
      (Merkle.Fold.merkleRoot hash2v Withdraw.Nullifier.C0 d indices path).val = rootOf (Hn hash2v) L ∧
      Omni p Γw st («withdraw-0.0.0::main».call h![]
        h![Withdraw.Nullifier.N0, (0 : Fp p), (0 : Fp p), (0 : Fp p),
          Merkle.Fold.merkleRoot hash2v Withdraw.Nullifier.C0 d indices path, (0 : Fp p), (0 : Fp p), d,
          path, indices])
        (fun r => ∃ st', r = some (st', ())) := by
  obtain ⟨d, I, P, hd, hr⟩ := complete_field hash2v L hN Withdraw.Nullifier.C0 hm
  refine ⟨d, P, I, hr, Withdraw.Root.main_accepting_execution_depth st d ?_ P I⟩
  rw [BitVec.le_def]
  simpa using hd

end Toy

/-- A one-leaf LeanIMT has the leaf as its root. -/
theorem sub_single (H : ℕ → ℕ → ℕ) (x : ℕ) : ∀ l, sub H l [x] = x
  | 0 => rfl
  | l + 1 => by
    simp only [sub]
    rw [if_pos (by simpa using Nat.one_le_two_pow)]
    exact sub_single H x l

theorem rootOf_single (H : ℕ → ℕ → ℕ) (x : ℕ) : rootOf H [x] = x := by
  rw [rootOf_eq_sub]; exact sub_single H x _

section NVT
open Determinism Transfer.HashGood Transfer.Forward Poseidon.Hash2

/-- **Non-vacuity of the T3 composition (depth 0).** The accepting execution `Transfer.Execution.main_accepting_execution` of the complete
extracted transfer `main` has `commitment_root = C0` at `proof_length_0 = 0`, and `C0.val` is the
contract root of the one-leaf tree `[C0.val]`: the premises of `transfer_member_or_bad` hold. -/
theorem transfer_tree_nonvacuous (st : State p) :
    Transfer.Execution.C0.val = rootOf (Hn hash2v) [Transfer.Execution.C0.val] ∧
      Omni p Γt st («transfer-0.0.0::main».call h![]
        h![Transfer.Execution.N0, Transfer.Execution.N1, Transfer.Execution.D0, Transfer.Execution.D0, Transfer.Execution.C0, (0 : Fp p), (0 : Fp p),
          (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p), (0 : U 128), (1 : Fp p), (0 : Fp p),
          (0 : U 128), (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : U 128), (0 : Fp p), (0 : Fp p),
          (0 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false,
          (33 : U 32), List.Vector.replicate 32 (0 : Fp p), List.Vector.replicate 32 false])
        (fun r => ∃ st', r = some (st', ())) :=
  ⟨(rootOf_single _ _).symm, Transfer.Execution.main_accepting_execution st⟩

end NVT

end FoldBridge
