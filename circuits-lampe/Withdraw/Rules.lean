import Withdraw.HashDeterminism
import Deposit.Commitment

/-!
Withdraw rules W2-W5 over the complete extracted withdraw `main`, on the patched Lampe (with
the pinned cast builtin).

Part 1 (relational, as in `Deposit.Rules`): every accepting execution of `main` passes through the
extracted `poseidon1`, `poseidon4`, `verify_merkle_proof<32>` (depth bound and Merkle root call)
and `poseidon2` calls with the arguments of the source, and the checks hold on their outcomes.

Part 2 (plain equations, as in `Deposit.Commitment`): with the withdraw certificates, the `Good`
proofs and the permutation forward functions, W3 and W5 become equations over the same pure functions as
the deposit rule 3 (`Deposit.Commitment.ownerKey`, `Deposit.Commitment.hash4`).
-/

namespace Withdraw.Rules
open Lampe Determinism Withdraw.HashGood Deposit.Rules

abbrev p := Crypto.Bn254.prime

theorem mem1 {Γ : Env} {decl : FunctionDecl}
    (h : Γ.functions.filter (fun d => d.name == decl.name) = [decl]) : decl ∈ Γ.functions := by
  have hm : decl ∈ Γ.functions.filter (fun d => d.name == decl.name) := by
    rw [h]; exact List.mem_singleton_self decl
  exact (List.mem_filter.mp hm).1

theorem mem3 {Γ : Env} {decl : FunctionDecl}
    (h : Γ.functions.filter (fun d => d.name == decl.name) = List.replicate 3 decl) :
    decl ∈ Γ.functions := by
  have hm : decl ∈ Γ.functions.filter (fun d => d.name == decl.name) := by
    rw [h]; exact List.mem_replicate.mpr ⟨by decide, rfl⟩
  exact (List.mem_filter.mp hm).1

set_option pp.deepTerms false in
set_option pp.maxSteps 2000 in
set_option maxHeartbeats 400000 in
theorem range_wit_w {p} (amount : Fp p) :
    Wit p Γw («std-1.0.0-beta.21::field::assert_max_bit_size».call h![(128 : U 32)] h![amount]) := by
  apply wit_call Withdraw.Lookup.range_unique
  dsimp only [«std-1.0.0-beta.21::field::assert_max_bit_size»]
  repeat' first
    | (apply wit_let_pure; intro)
    | (apply wit_let_cast; intro)
    | apply wit_let_constU
    | apply wit_let_litU
    | apply wit_skip

/-- The Merkle part of the withdraw check, stepped inside `verify_merkle_proof<32>`. -/
theorem vmp_rel {p} {st Q} (leaf root : Fp p) (proof_length : U 32)
    (indices : List.Vector Bool 32) (path : List.Vector (Fp p) 32)
    (hv : Omni p Γw st («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
      h![leaf, root, proof_length, indices, path]) Q) (hvn : ¬ Q none) :
    proof_length ≤ 32 ∧ ∃ st₅, Omni p Γw st₅
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          leaf, proof_length, indices, path])
      (fun r => ∃ st₆, r = some (st₆, root)) := by
  have hv0 := step_call (decl := «withdraw-0.0.0::verify_merkle_proof») (generics := h![(32 : U 32)])
    Withdraw.Lookup.vmp_unique hv
  dsimp only [«withdraw-0.0.0::verify_merkle_proof»] at hv0
  have hv1 := step_constU hv0
  obtain ⟨hle, hv2⟩ := step_assert (step_uLeq hv1 hvn) hvn
  simp only [decide_eq_true_eq] at hle
  refine ⟨hle, ?_⟩
  refine ⟨st, Omni.consequence (step_seq (step_fn (step_fn hv2)) hvn) ?_⟩
  rintro r ⟨st₅, root', rfl, hv3⟩
  obtain ⟨hr, _⟩ := step_assert (step_fEq hv3 hvn) hvn
  simp only [decide_eq_true_eq] at hr
  subst hr
  exact ⟨st₅, rfl⟩

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

/-- W2-W5, relational: in every accepting execution of the complete extracted withdraw `main`,
`poseidon1(spending_key)` has an outcome `owner`; after the range call, `poseidon4(token,
amount, owner, salt)` has an outcome `commitment`; then `proof_length ≤ 32`, the extracted
`binary_merkle_root(hash_2, commitment, proof_length, indices, path)` returns `commitment_root`,
and, on an outcome of `verify_merkle_proof`, `poseidon2(commitment, spending_key)` returns the
public `nullifier`. -/
theorem accepting_main_rel {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![spending_key])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        ∃ st₃, Omni p Γw st₃ («withdraw-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₄ commitment, r = some (st₄, commitment) ∧ proof_length ≤ 32 ∧
            (∃ st₅, Omni p Γw st₅
              («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
                h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                  commitment, proof_length, indices, path])
              (fun r => ∃ st₆, r = some (st₆, commitment_root))) ∧
            Omni p Γw st₄ («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
                h![commitment, commitment_root, proof_length, indices, path])
              (fun r => ∃ st₇ u, r = some (st₇, u) ∧
                Omni p Γw st₇ («withdraw-0.0.0::poseidon2».call h![] h![commitment, spending_key])
                  (fun r => ∃ st₈, r = some (st₈, nullifier))))) := by
  have h0 := step_call Withdraw.Lookup.main_unique accepts
  have h1 := step_fn h0
  refine Omni.consequence (step_seq h1 rejects_failure) ?_
  rintro r ⟨st₂, owner, rfl, h2⟩
  refine ⟨st₂, owner, rfl, ?_⟩
  obtain ⟨st₃, _, h3⟩ := (range_wit_w amount).run (step_seq (step_fn h2) rejects_failure)
    (fun h => by simp at h)
  obtain ⟨st₃', _, hst, h4⟩ := h3
  cases hst
  refine ⟨st₃, ?_⟩
  refine Omni.consequence (step_seq (step_fn h4) rejects_failure) ?_
  rintro r ⟨st₄, cm, rfl, h5⟩
  refine ⟨st₄, cm, rfl, ?_⟩
  obtain ⟨Qv, hv, hvn, hk⟩ := letIn_inv (step_fn h5) rejects_failure
  obtain ⟨hle, hroot⟩ := vmp_rel cm commitment_root proof_length indices path hv hvn
  refine ⟨hle, hroot, ?_⟩
  refine Omni.consequence hv ?_
  intro r hr
  cases r with
  | none => exact absurd hr hvn
  | some sv =>
    obtain ⟨st₇, u⟩ := sv
    refine ⟨st₇, u, rfl, ?_⟩
    have h6 := hk u st₇ hr
    refine Omni.consequence (step_seq (step_fn h6) rejects_failure) ?_
    rintro r ⟨st₈, nf, rfl, h7⟩
    obtain ⟨hc, _⟩ := step_assert (step_fEq h7 rejects_failure) rejects_failure
    simp only [decide_eq_true_eq] at hc
    subst hc
    exact ⟨st₈, rfl⟩

/-! ## Part 2: plain equations for W3 and W5 -/

theorem bn254_gt : 2 ^ 32 < p.natVal := by decide

section
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

theorem perm2w : Poseidon.Wrappers.Perm2 Γw Deposit.Main.f2 := by
  intro st v
  exact Poseidon.Permutation2.run st _ _ _ _ v (mem1 Withdraw.Lookup.permute_filter) (mem1 Withdraw.Lookup.sigma_filter)
    (mem1 Withdraw.Lookup.apply_matrix_filter) (mem3 Withdraw.Lookup.pow_32_filter) (mem3 Withdraw.Lookup.to_le_bits_filter)

theorem perm5w : Poseidon.Wrappers.Perm5 Γw Deposit.Main.f5 := by
  intro st v
  exact Poseidon.Permutation5.run st _ _ _ _ v (mem1 Withdraw.Lookup.permute_filter) (mem1 Withdraw.Lookup.sigma_filter)
    (mem1 Withdraw.Lookup.apply_matrix_filter) (mem3 Withdraw.Lookup.pow_32_filter) (mem3 Withdraw.Lookup.to_le_bits_filter)

theorem x5_2_fwd (s : State p) (v : List.Vector (Fp p) 2) :
    Omni p Γw s («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v])
      (fun r => ∃ st', r = some (st', Deposit.Main.f2 v)) := by
  apply Omni.consequence (Poseidon.Wrappers.wrapper2 s v Deposit.Main.f2 perm2w
    (mem1 Withdraw.Lookup.x5_2_filter) (mem1 Withdraw.Lookup.x5_2_config_filter) (mem1 Withdraw.Lookup.config_filter)
    (mem1 Withdraw.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem x5_5_fwd (s : State p) (v : List.Vector (Fp p) 5) :
    Omni p Γw s («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (fun r => ∃ st', r = some (st', Deposit.Main.f5 v)) := by
  apply Omni.consequence (Poseidon.Wrappers.wrapper5 s v Deposit.Main.f5 perm5w
    (mem1 Withdraw.Lookup.x5_5_filter) (mem1 Withdraw.Lookup.x5_5_config_filter) (mem1 Withdraw.Lookup.config_filter)
    (mem1 Withdraw.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem poseidon1_fwd (st : State p) (a : Fp p) :
    Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![a])
      (fun r => ∃ st', r = some (st', Deposit.Commitment.ownerKey a)) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.poseidon1_filter)
  dsimp only [«withdraw-0.0.0::poseidon1»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((1 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact (Poseidon.Hash.hash1 a Deposit.Main.f2 (mem1 Withdraw.Lookup.hash_1_filter)
      (mem1 Withdraw.Lookup.hash_internal_filter) x5_2_fwd)

theorem poseidon4_fwd (st : State p) (a b c d : Fp p) :
    Omni p Γw st («withdraw-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', Deposit.Commitment.hash4 a b c d)) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.poseidon4_filter)
  dsimp only [«withdraw-0.0.0::poseidon4»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((4 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact (Poseidon.Hash.hash4 a b c d Deposit.Main.f5 (mem1 Withdraw.Lookup.hash_4_filter)
      (mem1 Withdraw.Lookup.hash_internal_filter) x5_5_fwd)
end

/-- Every derivation of the extracted withdraw `poseidon1(a)` has an outcome with value
`ownerKey a`. -/
theorem poseidon1_pinned {st Q} (a : Fp p)
    (h : Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![a]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.ownerKey a)) :=
  (wgood_poseidon1 bn254_gt a).pin (poseidon1_fwd st a) h

/-- Every derivation of the extracted withdraw `poseidon4(a, b, c, d)` has an outcome with value
`hash4 a b c d`. -/
theorem poseidon4_pinned {st Q} (a b c d : Fp p)
    (h : Omni p Γw st («withdraw-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.hash4 a b c d)) :=
  (wgood_poseidon4 bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

/-- W3 and W5 as plain values, with W2 and W4 relational on the plain commitment: in every
accepting execution of the complete extracted withdraw `main`, the note commitment is
`hash4 token amount (ownerKey spending_key) salt` (PUBLIC token and amount, owner key from the
private spending key); `proof_length ≤ 32`; the extracted Merkle root call on that commitment
returns `commitment_root`; and on an outcome of `verify_merkle_proof` the extracted
`poseidon2(commitment, spending_key)` returns the public `nullifier`. -/
theorem accepting_main_rules_eq {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₄, proof_length ≤ 32 ∧
      (∃ st₅, Omni p Γw st₅
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt,
            proof_length, indices, path])
        (fun r => ∃ st₆, r = some (st₆, commitment_root))) ∧
      Omni p Γw st₄ («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
          h![Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt,
            commitment_root, proof_length, indices, path])
        (fun r => ∃ st₇ u, r = some (st₇, u) ∧
          Omni p Γw st₇ («withdraw-0.0.0::poseidon2».call h![] h![
              Deposit.Commitment.hash4 token amount (Deposit.Commitment.ownerKey spending_key) salt, spending_key])
            (fun r => ∃ st₈, r = some (st₈, nullifier))) := by
  have h := accepting_main_rel nullifier token amount recipient commitment_root spending_key salt
    proof_length path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, st₃, h2⟩ := poseidon1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₄, cm, heq4, hle, hroot, hv⟩ := poseidon4_pinned _ _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq4)
  exact ⟨_, hle, hroot, hv⟩

#print axioms mem1
#print axioms mem3
#print axioms range_wit_w
#print axioms vmp_rel
#print axioms accepting_main_rel
#print axioms bn254_gt
#print axioms perm2w
#print axioms perm5w
#print axioms x5_2_fwd
#print axioms x5_5_fwd
#print axioms poseidon1_fwd
#print axioms poseidon4_fwd
#print axioms poseidon1_pinned
#print axioms poseidon4_pinned
#print axioms accepting_main_rules_eq
end Withdraw.Rules
