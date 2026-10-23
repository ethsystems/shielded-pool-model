import Merkle.Fold
import Deposit.MerkleLookup
import Poseidon.Hash2

/-!
Deposit rule 4 as a plain equation. In the DEPOSIT environment: four new `UniqueDecl`
certificates (`Deposit.MerkleLookup`: hash_2, x5_3, x5_3_config, binary_merkle_root), the `Good` proofs of
the width-3 path and of `binary_merkle_root<20>` (the `Withdraw.HashDeterminism` bodies with the deposit
certificates and the deposit `Good` proofs of `Determinism.DepositHash`), the width-3 forward result (`Poseidon.Hash2.wrapper3`
and `Poseidon.Hash2.hash2` are environment-generic; the memberships come from the certificates), and
`Merkle.Fold.bmr_fwd` at `N = 20`.
-/

namespace Deposit.AttestationRoot
open Lampe Determinism

section
variable {p : Prime}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem dgood_x5_3_config :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».call h![] h![]) := by
  apply Good.call Deposit.MerkleLookup.x5_3_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_3_config»]
  repeat' first
    | exact good_literalArray
    | exact good_alpha
    | exact good_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem dgood_x5_3 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 3)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v]) := by
  apply Good.call Deposit.MerkleLookup.x5_3_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_3»]
  repeat' first
    | exact dgood_x5_3_config
    | exact good_permute_c hp _ _ _ _ _
    | good_step

theorem dgood_internal2 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 2)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(2 : U 32), (3 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name [] h![] ]) := by
  apply Good.call Deposit.HashLookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact dgood_x5_3 hp _
    | good_step

theorem dgood_hash_2 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 2)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_2».call h![] h![input]) := by
  apply Good.call Deposit.MerkleLookup.hash_2_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_2»]
  repeat' first
    | exact dgood_internal2 hp _
    | good_step

theorem dgood_bmr (hp : 2 ^ 32 < p.natVal) (leaf : Fp p) (depth : U 32)
    (indices : Tp.denote p (.array .bool 20)) (siblings : Tp.denote p (.array .field 20)) :
    Good p Γd («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
      h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, siblings]) := by
  apply Good.call Deposit.MerkleLookup.bmr_unique
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  repeat' first
    | exact dgood_hash_2 hp _
    | (apply Good.builtin; exact bdet_uLt)
    | good_step
end

section
open Deposit.Commitment Poseidon.Hash2 Merkle.Fold
set_option backward.isDefEq.respectTransparency false

theorem perm3d : Perm3 Γd f3 := by
  intro st v
  exact Poseidon.Permutation3.run st _ _ _ _ v (Withdraw.Rules.mem1 Deposit.HashLookup.permute_filter) (Withdraw.Rules.mem1 Deposit.HashLookup.sigma_filter)
    (Withdraw.Rules.mem1 Deposit.HashLookup.apply_matrix_filter) (Withdraw.Rules.mem3 Deposit.HashLookup.pow_32_filter)
    (Withdraw.Rules.mem3 Deposit.HashLookup.to_le_bits_filter)

theorem x5_3_fwd_d (s : State p) (v : List.Vector (Fp p) 3) :
    Omni p Γd s («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (fun r => ∃ st', r = some (st', f3 v)) := by
  apply Omni.consequence (wrapper3 s v f3 perm3d
    (Withdraw.Rules.mem1 Deposit.MerkleLookup.x5_3_filter) (Withdraw.Rules.mem1 Deposit.MerkleLookup.x5_3_config_filter) (Withdraw.Rules.mem1 Deposit.ConfigLookup.config_filter)
    (Withdraw.Rules.mem1 Deposit.HashLookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem hash_2_fwd_d (st : State p) (a b : Fp p) :
    Omni p Γd st («poseidon-0.0.0::poseidon::bn254::hash_2».call h![]
      h![(⟨[a,b],rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', hash2v a b)) :=
  hash2 a b f3 (Withdraw.Rules.mem1 Deposit.MerkleLookup.hash_2_filter) (Withdraw.Rules.mem1 Deposit.HashLookup.hash_internal_filter) x5_3_fwd_d

theorem bmr_fwd_d (st : State p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 20) (path : List.Vector (Fp p) 20) :
    Omni p Γd st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', merkleRoot hash2v leaf depth indices path)) :=
  bmr_fwd (20 : U 32) hash2v _ (Withdraw.Rules.mem1 Deposit.MerkleLookup.bmr_filter) (fun st a b => hash_2_fwd_d st a b)
    st leaf depth indices path

theorem bmr_pinned_d {st Q} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool 20) (path : List.Vector (Fp p) 20)
    (h : Omni p Γd st
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, path]) Q) :
    ∃ st', Q (some (st', merkleRoot hash2v leaf depth indices path)) :=
  (dgood_bmr bn254_gt leaf depth indices path).pin (bmr_fwd_d st leaf depth indices path) h

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

/-- Deposit rules 3 and 4 as equations on the complete extracted deposit `main`: in every
accepting execution the commitment is `hash4 token amount (ownerKey spending_key) salt`,
`proof_length ≤ 20`, and the public `attestation_root` is the Merkle fold (`hash2v`, 20 levels,
active up to `proof_length`) of the attestation leaf
`hash4 (ownerKey spending_key) attester issued_at expires_at`. -/
theorem accepting_main_attestation_root {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt ∧ proof_length ≤ 20 ∧
      attestation_root = merkleRoot hash2v
        (hash4 (ownerKey spending_key) attester ((issued_at.toNat : ℕ) : Fp p)
          ((expires_at.toNat : ℕ) : Fp p)) proof_length indices path := by
  obtain ⟨hc, hle, st₄, hroot⟩ := accepting_main_rules_eq commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length path
    indices accepts rejects_failure
  obtain ⟨st', st₅, heq⟩ := bmr_pinned_d _ _ _ _ hroot
  exact ⟨hc, hle, (Prod.mk.inj (Option.some.inj heq)).2.symm⟩
end

#print axioms dgood_x5_3_config
#print axioms dgood_x5_3
#print axioms dgood_internal2
#print axioms dgood_hash_2
#print axioms dgood_bmr
#print axioms perm3d
#print axioms x5_3_fwd_d
#print axioms hash_2_fwd_d
#print axioms bmr_fwd_d
#print axioms bmr_pinned_d
#print axioms accepting_main_attestation_root
end Deposit.AttestationRoot
