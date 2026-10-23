import Deposit.Attestation
import Lampe.Crypto.Bn254.Prime

/-!
The patched cast builtin has one function per type pair.

* `cast_det`: two derivations of one cast share an outcome.
* `cast_u64_field`: every derivation of `v as Field` for `v : u64` returns `v.toNat` in the
  input state.
* `cast_not_unconstrained`: the counterexample of the unpatched builtin (`5 as Field` returning
  `0`) has no derivation. Its theorem `cast_unconstrained` is kept as a control that must not compile.
* `accepting_main_rules_pinned`: rules 2, 3 and 4 with the leaf's timestamps pinned to
  `issued_at.toNat` and `expires_at.toNat`.
-/

namespace Deposit.PinnedCast
open Lampe Deposit.Rules

theorem cast_det {p Γ st tp tp'} {v : Tp.denote p tp} {Q₁ Q₂}
    (h₁ : Omni p Γ st (.callBuiltin [tp] tp' Builtin.cast h![v]) Q₁)
    (h₂ : Omni p Γ st (.callBuiltin [tp] tp' Builtin.cast h![v]) Q₂) :
    ∃ r, Q₁ r ∧ Q₂ r := by
  cases h₁ with
  | callBuiltin h₁ =>
    cases h₂ with
    | callBuiltin h₂ =>
      obtain ⟨_, hq₁⟩ := Builtin.castOmni_inv h₁
      obtain ⟨_, hq₂⟩ := Builtin.castOmni_inv h₂
      exact ⟨_, hq₁, hq₂⟩

theorem cast_u64_field {p Γ st} {v : U 64} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 64] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

theorem cast_not_unconstrained {Γ} (st : State Crypto.Bn254.prime) :
    ¬ Omni Crypto.Bn254.prime Γ st (.callBuiltin [.u 64] .field Builtin.cast h![(5 : U 64)])
        (fun r => r = some (st, (0 : Fp Crypto.Bn254.prime))) := by
  intro h
  have h5 := cast_u64_field h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h5
  have hv : ((5 : U 64).toNat : ℕ) = 5 := by decide
  rw [hv] at h5
  have hval := congrArg ZMod.val h5
  rw [ZMod.val_natCast, ZMod.val_zero] at hval
  have hlt : 5 < Crypto.Bn254.prime.natVal := by decide
  rw [Nat.mod_eq_of_lt hlt] at hval
  exact absurd hval (by decide)

theorem step_cast_pinned {p Γ st tp tp' tp''} [Builtin.CastTp tp tp'] {v : Tp.denote p tp}
    {b : Tp.denote p tp' → Expr (Tp.denote p) tp''} {Q}
    (h : Omni p Γ st (.letIn (.callBuiltin [tp] tp' Builtin.cast h![v]) b) Q) :
    Omni p Γ st (b (Builtin.CastTp.cast v)) Q := by
  obtain ⟨_, h'⟩ := step_cast h
  exact h'

variable {p : Prime}
variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

/-- Rules 2, 3 and 4 jointly on the patched Lampe: the leaf's timestamp arguments are now the
canonical casts `issued_at.toNat` and `expires_at.toNat`. -/
theorem accepting_main_rules_pinned {st Q}
    (accepts : Omni p «deposit-0.0.0».env st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₁, Omni p «deposit-0.0.0».env st₁
      («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
        h![(⟨[spending_key], rfl⟩ : List.Vector (Fp p) 1)])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        Omni p «deposit-0.0.0».env st₂
          («deposit-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₃, r = some (st₃, commitment) ∧
            Omni p «deposit-0.0.0».env st₃
              («deposit-0.0.0::poseidon4».call h![]
                h![owner, attester, ((issued_at.toNat : ℕ) : Fp p), ((expires_at.toNat : ℕ) : Fp p)])
              (fun r => ∃ st₄ leaf, r = some (st₄, leaf) ∧ proof_length ≤ 20 ∧
                Omni p «deposit-0.0.0».env st₄
                  («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
                    h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                      leaf, proof_length, indices, path])
                  (fun r => ∃ st₅, r = some (st₅, attestation_root))))) := by
  have h0 := step_call Deposit.Range.main_unique accepts
  have h1 := step_fn h0
  obtain ⟨st₁, _, h2⟩ := (range_wit amount).run (step_seq h1 rejects_failure)
    (fun h => by simp at h)
  obtain ⟨st₁', _, hst, h3⟩ := h2
  cases hst
  refine ⟨st₁, ?_⟩
  have h4 := step_mkArray1 (step_fn h3) rejects_failure
  refine Omni.consequence (step_seq h4 rejects_failure) ?_
  rintro r ⟨st₂, owner, rfl, h5⟩
  refine ⟨st₂, owner, rfl, ?_⟩
  refine Omni.consequence (step_seq (step_fn h5) rejects_failure) ?_
  rintro r ⟨st₃, cc, rfl, h6⟩
  obtain ⟨hc, h7⟩ := step_assert (step_fEq h6 rejects_failure) rejects_failure
  simp only [decide_eq_true_eq] at hc
  subst hc
  refine ⟨st₃, rfl, ?_⟩
  have h8 := step_cast_pinned (tp := .u 64) (tp' := .field) (step_fn h7)
  have h9 := step_cast_pinned (tp := .u 64) (tp' := .field) h8
  refine Omni.consequence (step_seq h9 rejects_failure) ?_
  rintro r ⟨st₄, leaf, rfl, h10⟩
  refine ⟨st₄, leaf, rfl, ?_⟩
  obtain ⟨Qv, hv, hvn, _⟩ := letIn_inv (step_fn h10) rejects_failure
  have hv0 := step_call (decl := «deposit-0.0.0::verify_merkle_proof») (generics := h![(20 : U 32)])
    verify_unique hv
  dsimp only [«deposit-0.0.0::verify_merkle_proof»] at hv0
  have hv1 := step_constU hv0
  obtain ⟨hle, hv2⟩ := step_assert (step_uLeq hv1 hvn) hvn
  simp only [decide_eq_true_eq] at hle
  refine ⟨hle, ?_⟩
  refine Omni.consequence (step_seq (step_fn (step_fn hv2)) hvn) ?_
  rintro r ⟨st₅, root', rfl, hv3⟩
  obtain ⟨hr, _⟩ := step_assert (step_fEq hv3 hvn) hvn
  simp only [decide_eq_true_eq] at hr
  subst hr
  exact ⟨st₅, rfl⟩

#print axioms cast_det
#print axioms cast_u64_field
#print axioms cast_not_unconstrained
#print axioms step_cast_pinned
#print axioms accepting_main_rules_pinned
end Deposit.PinnedCast
