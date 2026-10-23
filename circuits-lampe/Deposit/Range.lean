import «deposit-0.0.0».Extracted
import Lampe
import Deposit.MainLookup
import Semantics.Builtins

namespace Deposit.Range
open Lampe

-- A necessary condition for any execution whose postcondition rejects failure.
@[irreducible] def Guard (p : Prime) (Γ : Env) (e : Expr (Tp.denote p) tp) (R : Prop) : Prop :=
  ∀ st Q, Omni p Γ st e Q → ¬ Q none → R

theorem pure_outcome {A : Type} {sgn : A → List Tp × Tp} {desc p Γ st argTps outTp args Q}
    (h : Omni p Γ st (.callBuiltin argTps outTp (Builtin.newGenericPureBuiltin sgn desc) args) Q) :
    Q none ∨ ∃ v, Q (some (st, v)) := by
  cases h with
  | callBuiltin h =>
    cases h with
    | ok _ h => exact Or.inr ⟨_, h⟩
    | err _ h => exact Or.inl h

theorem guard_let_pure {A : Type} {sgn : A → List Tp × Tp} {desc p Γ argTps outTp args}
    {tp} {b : Tp.denote p outTp → Expr (Tp.denote p) tp} {R}
    (next : ∀ v, Guard p Γ (b v) R) :
    Guard p Γ (.letIn (.callBuiltin argTps outTp (Builtin.newGenericPureBuiltin sgn desc) args) b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he hb hf =>
    rcases pure_outcome he with hfail | ⟨v, hv⟩
    · exact False.elim (hn (hf hfail))
    · exact next v st Q (hb v st hv) hn

theorem guard_let_fn {p Γ argTps outTp} {r : FuncRef argTps outTp}
    {tp} {b : Tp.denote p (.fn argTps outTp) → Expr (Tp.denote p) tp} {R}
    (next : Guard p Γ (b r) R) : Guard p Γ (.letIn (.fn argTps outTp r) b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he hb _ => cases he with | «fn» hv => exact next st Q (hb _ _ hv) hn

theorem guard_let_constU {p Γ w} {v : U w}
    {tp} {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp} {R}
    (next : Guard p Γ (b v) R) : Guard p Γ (.letIn (.constU v) b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he hb _ => cases he with | constU hv => exact next st Q (hb _ _ hv) hn

theorem guard_let_litU {p Γ w} {v : Int}
    {tp} {b : Tp.denote p (.u w) → Expr (Tp.denote p) tp} {R}
    (next : Guard p Γ (b (BitVec.ofInt w v)) R) : Guard p Γ (.letIn (.litNum (.u w) v) b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he hb _ => cases he with | litU hv => exact next st Q (hb _ _ hv) hn

theorem guard_prefix {p Γ tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {R}
    (first : Guard p Γ e R) : Guard p Γ (.letIn e b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he _ hf => exact first st _ he (fun hfail => hn (hf hfail))

theorem range_builtin_guard {p Γ} {amount : Fp p} {bits : U 32} :
    Guard p Γ (.callBuiltin [.field, .u 32] .unit Builtin.applyRangeConstraint h![amount, bits])
      (amount.val < 2 ^ bits.toNat) := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | callBuiltin h =>
    cases h with
    | ok h _ => exact h
    | err _ h => exact False.elim (hn h)

theorem guard_let_cast {p Γ source target} {v : Tp.denote p source}
    {tp} {b : Tp.denote p target → Expr (Tp.denote p) tp} {R}
    (next : ∀ v, Guard p Γ (b v) R) :
    Guard p Γ (.letIn (.callBuiltin [source] target Builtin.cast h![v]) b) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | letIn he hb _ =>
    cases he with
    | callBuiltin hc =>
      cases hc with
      | ok hv => exact next _ st Q (hb _ _ hv) hn

set_option maxHeartbeats 200000 in
theorem range_body_guard {p Γ} (amount : Fp p) (bits : U 32) :
    Guard p Γ
      ((«std-1.0.0-beta.21::field::assert_max_bit_size».fn.body (Tp.denote p) h![bits]).body h![amount])
      (amount.val < 2 ^ bits.toNat) := by
  dsimp only [«std-1.0.0-beta.21::field::assert_max_bit_size»]
  repeat' first
    | (apply guard_prefix; exact range_builtin_guard)
    | apply guard_let_constU
    | apply guard_let_litU
    | (apply guard_let_cast; intro)
    | (apply guard_let_pure; intro)

@[irreducible] def UniqueDecl (Γ : Env) (decl : FunctionDecl) : Prop :=
  ∀ f, ⟨decl.name, f⟩ ∈ Γ.functions → f = decl.fn

theorem guard_decl {p Γ kinds} {generics : HList Kind.denote kinds} {argTps outTp args fnName R}
    (bodies : ∀ f, ⟨fnName, f⟩ ∈ Γ.functions →
      ∀ (hk : f.generics = kinds)
        (hi : (f.body (Tp.denote p) (hk ▸ generics)).argTps = argTps)
        (ho : (f.body (Tp.denote p) (hk ▸ generics)).outTp = outTp),
        Guard p Γ (ho ▸ (f.body (Tp.denote p) (hk ▸ generics)).body (hi ▸ args)) R) :
    Guard p Γ (.call argTps outTp (.decl fnName kinds generics) args) R := by
  unfold Guard at *
  intro st Q h hn
  cases h with
  | callTrait href _ _ _ _ _ => cases href
  | callLambda href _ _ => cases href
  | callDecl href hmem hk hi ho he =>
    cases href
    exact bodies _ hmem hk hi ho _ _ he hn

theorem guard_call {p Γ decl generics args R}
    (unique : UniqueDecl Γ decl)
    (body : Guard p Γ ((decl.fn.body (Tp.denote p) generics).body args) R) :
    Guard p Γ (decl.call generics args) R := by
  apply guard_decl
  intro f hm hk hi ho
  unfold UniqueDecl at unique
  have heq := unique f hm
  subst f
  simpa using body

theorem range_call_guard {p Γ} (amount : Fp p) (bits : U 32)
    (unique : UniqueDecl Γ «std-1.0.0-beta.21::field::assert_max_bit_size») :
    Guard p Γ («std-1.0.0-beta.21::field::assert_max_bit_size».call h![bits] h![amount])
      (amount.val < 2 ^ bits.toNat) :=
  guard_call unique (range_body_guard amount bits)

theorem unique_of_filter {Γ : Env} {decl : FunctionDecl} {n : Nat}
    (h : Γ.functions.filter (fun d => d.name == decl.name) = List.replicate n decl) : UniqueDecl Γ decl := by
  unfold UniqueDecl
  intro f hm
  have : (⟨decl.name, f⟩ : FunctionDecl) ∈ Γ.functions.filter (fun d => d.name == decl.name) := by
    exact List.mem_filter.mpr ⟨hm, by simp⟩
  rw [h] at this
  have hd := List.eq_of_mem_replicate this
  exact congrArg FunctionDecl.fn hd

#print axioms unique_of_filter
theorem range_unique : UniqueDecl «deposit-0.0.0».env
    «std-1.0.0-beta.21::field::assert_max_bit_size» :=
  unique_of_filter (n := 3) Deposit.MainLookup.range_filter

theorem main_unique : UniqueDecl «deposit-0.0.0».env «deposit-0.0.0::main» :=
  unique_of_filter (n := 1) Deposit.MainLookup.main_filter

-- This proves a dependency call, not a call made by deposit main.
theorem poseidon2_dependency_execution {p st} (input : List.Vector (Fp p) 4) :
    Omni p «deposit-0.0.0».env st
      («std-1.0.0-beta.21::hash::poseidon2_permutation».call h![(4 : U 32)] h![input])
      (fun r => r = some (st, Crypto.Poseidon2.noirPermutation4 input)) := by
  apply Omni.is_mono (Γ₁ := «std-1.0.0-beta.21».env) (by solve_env_subset)
  exact Semantics.Builtins.permutation_nonvacuous input

#print axioms poseidon2_dependency_execution

variable {p : Prime} {Γ : Env}
variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem main_body_amount_bound
    (unique : UniqueDecl Γ «std-1.0.0-beta.21::field::assert_max_bit_size») :
    Guard p Γ
      ((«deposit-0.0.0::main».fn.body (Tp.denote p) h![]).body
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices])
      (amount.val < 2 ^ 128) := by
  dsimp only [«deposit-0.0.0::main»]
  apply guard_let_fn
  apply guard_prefix
  exact range_call_guard amount (128 : U 32) unique

theorem accepting_main_amount_bound {st Q}
    (accepts : Omni p «deposit-0.0.0».env st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) : amount.val < 2 ^ 128 := by
  have h := guard_call main_unique
    (main_body_amount_bound commitment token amount funding_address attestation_root payload_hash
      spending_key salt attester issued_at expires_at proof_length path indices range_unique)
  unfold Guard at h
  exact h st Q accepts rejects_failure

#print axioms range_unique
#print axioms main_unique
#print axioms accepting_main_amount_bound
#print axioms unique_of_filter
#print axioms main_body_amount_bound
#print axioms range_call_guard
#print axioms guard_let_cast
#print axioms guard_decl
#print axioms guard_call
#print axioms range_body_guard
#print axioms pure_outcome
#print axioms guard_let_pure
#print axioms guard_let_fn
#print axioms guard_let_constU
#print axioms guard_let_litU
#print axioms guard_prefix
#print axioms range_builtin_guard
end Deposit.Range
