import Determinism.DepositHash
import Deposit.PinnedCast
import Deposit.Main

/-!
Rules 2 and 3 of the deposit circuit, and rule 4's leaf, as plain equations over the
complete extracted `main` on BN254. The hash values are the pure forward functions of the
permutation proofs: `Deposit.Main.f2` (= `Poseidon.Permutation2.f`, the width-2 permutation) and `Deposit.Main.f5`
(= `Poseidon.Permutation5.f`), read through `Deposit.MainPermutations.hash4`. No claim about Poseidon's
cryptographic properties.
-/

namespace Deposit.Commitment
open Lampe Determinism

abbrev p := Crypto.Bn254.prime
abbrev Γ := «deposit-0.0.0».env

theorem bn254_gt : 2 ^ 32 < p.natVal := by decide

/-- The owner key that the extracted `hash_1([sk])` computes (the permutation forward function). -/
def ownerKey (sk : Fp p) : Fp p := (Deposit.Main.f2 ⟨[0, sk], rfl⟩).get ⟨0, by decide⟩

/-- The value that the extracted `poseidon4(a, b, c, d)` computes (the permutation forward function). -/
abbrev hash4 (a b c d : Fp p) : Fp p := Deposit.MainPermutations.hash4 Deposit.Main.f5 a b c d

theorem hash_1_fwd (st : State p) (sk : Fp p) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[sk], rfl⟩ : List.Vector (Fp p) 1)]) (fun r => ∃ st', r = some (st', ownerKey sk)) := by
  apply Poseidon.Hash.hash1 sk Deposit.Main.f2 Deposit.Members.hash1 Deposit.Members.internal
  intro s v
  apply Omni.consequence (Poseidon.Wrappers.wrapper2 s v Deposit.Main.f2 Poseidon.Permutation2.perm
    Deposit.Members.wrapper2 Deposit.Members.config2 Deposit.Members.config Deposit.Members.alpha)
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem poseidon4_fwd (st : State p) (a b c d : Fp p) :
    Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', hash4 a b c d)) :=
  (Deposit.MainPermutations.hashes_from_permutations Deposit.Main.f2 Deposit.Main.f5 Poseidon.Permutation2.perm
    Poseidon.Permutation5.perm).2 st a b c d

/-- Every derivation of the extracted `hash_1([sk])` has an outcome with value `ownerKey sk`. -/
theorem hash_1_pinned {st Q} (sk : Fp p)
    (h : Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[sk], rfl⟩ : List.Vector (Fp p) 1)]) Q) : ∃ st', Q (some (st', ownerKey sk)) :=
  (good_hash_1 bn254_gt _).pin (hash_1_fwd st sk) h

/-- Every derivation of the extracted `poseidon4(a, b, c, d)` has an outcome with value
`hash4 a b c d`. -/
theorem poseidon4_pinned {st Q} (a b c d : Fp p)
    (h : Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', hash4 a b c d)) :=
  (good_poseidon4 bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

/-- Rule 2 with the owner key as a plain value: in every accepting execution the commitment
check of `main` succeeds with the owner key `ownerKey spending_key`, from an outcome state of the
extracted `hash_1([spending_key])` call. With `hash_1_pinned`, every derivation of that call has
an outcome with value `ownerKey spending_key`. -/
theorem accepting_main_owner_key {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₂, Omni p Γ st₂
      («deposit-0.0.0::poseidon4».call h![] h![token, amount, ownerKey spending_key, salt])
      (fun r => ∃ st₃, r = some (st₃, commitment)) := by
  obtain ⟨st₁, h⟩ := Deposit.Rules.accepting_main_commitment commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length
    path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  exact ⟨_, h2⟩

/-- Rule 3 as a plain equation: in every accepting execution of the complete extracted `main`,
`commitment = hash4 token amount (ownerKey spending_key) salt`. -/
theorem accepting_main_commitment_eq {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt := by
  obtain ⟨st₁, h⟩ := Deposit.Rules.accepting_main_commitment commitment token amount funding_address
    attestation_root payload_hash spending_key salt attester issued_at expires_at proof_length
    path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₃, heq3⟩ := poseidon4_pinned _ _ _ _ h2
  exact (Prod.mk.inj (Option.some.inj heq3)).2.symm

/-- Rules 3 and 4 jointly as equations: the commitment equation, the depth bound, and the
extracted Merkle root call on the leaf `hash4 (ownerKey spending_key) attester issued_at
expires_at`, which returns `attestation_root`. The root itself stays relational here (hash_2 and the
width-3 permutation come in `Deposit.AttestationRoot`). -/
theorem accepting_main_rules_eq {st Q}
    (accepts : Omni p Γ st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    commitment = hash4 token amount (ownerKey spending_key) salt ∧ proof_length ≤ 20 ∧
      ∃ st₄, Omni p Γ st₄
        («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
          h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
            hash4 (ownerKey spending_key) attester ((issued_at.toNat : ℕ) : Fp p)
              ((expires_at.toNat : ℕ) : Fp p), proof_length, indices, path])
        (fun r => ∃ st₅, r = some (st₅, attestation_root)) := by
  obtain ⟨st₁, h⟩ := Deposit.PinnedCast.accepting_main_rules_pinned commitment token amount
    funding_address attestation_root payload_hash spending_key salt attester issued_at expires_at
    proof_length path indices accepts rejects_failure
  obtain ⟨_, st₂, owner, heq, h2⟩ := hash_1_pinned spending_key h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  obtain ⟨_, st₃, heq3, h3⟩ := poseidon4_pinned _ _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq3)
  obtain ⟨_, st₄, leaf, heq4, hle, h4⟩ := poseidon4_pinned _ _ _ _ h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq4)
  exact ⟨rfl, hle, _, h4⟩

/-- The premises of the rule theorems are satisfiable: the accepting execution `Deposit.Main.main_accepting_execution` of the
complete extracted `main` (commitment `hash4 0 0 (ownerKey 0) 0`) meets them. -/
theorem rules_eq_nonvacuous (st : State p) :
    Deposit.MainPermutations.hash4 Deposit.Main.f5 0 0 (Deposit.MainPermutations.owner Deposit.Main.f2) 0 =
      hash4 0 0 (ownerKey 0) 0 ∧ (0 : U 32) ≤ 20 :=
  let h := accepting_main_rules_eq (Deposit.MainPermutations.hash4 Deposit.Main.f5 0 0 (Deposit.MainPermutations.owner Deposit.Main.f2) 0)
    0 0 0 (Deposit.MainPermutations.hash4 Deposit.Main.f5 (Deposit.MainPermutations.owner Deposit.Main.f2) 0 0 0) 0 0 0 0 0 0 0
    (List.Vector.replicate 20 0) (List.Vector.replicate 20 false)
    (Deposit.Main.main_accepting_execution st) (by rintro ⟨_, h⟩; cases h)
  ⟨h.1, h.2.1⟩

#print axioms bn254_gt
#print axioms hash_1_fwd
#print axioms poseidon4_fwd
#print axioms hash_1_pinned
#print axioms poseidon4_pinned
#print axioms accepting_main_owner_key
#print axioms accepting_main_commitment_eq
#print axioms accepting_main_rules_eq
#print axioms rules_eq_nonvacuous
end Deposit.Commitment
