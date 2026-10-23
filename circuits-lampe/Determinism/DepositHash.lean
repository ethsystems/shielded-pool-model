import Determinism.Bits
import Deposit.HashLookup

/-!
`Good` proofs (every two accepting derivations share an outcome) for the extracted hash
code that the deposit `main` reaches through `hash_1` and `poseidon4`: std `to_le_bits<32>` and
`pow_32`, Poseidon `sigma`, `apply_matrix`, `permute`, the width-2 and width-5 constants and
permutation wrappers, `hash_internal` at the two function references it is called with,
`hash_1`, `hash_4`, and deposit `poseidon4`. The proofs traverse the extracted bodies with the
`Good` constructors; calls go through the `UniqueDecl` certificates of `Deposit.HashLookup`.
-/

namespace Determinism
open Lampe

abbrev Γd := «deposit-0.0.0».env

/-- The tuple projection that the DSL emits for `let (a, b, …) = t` (`Expr.getMember`). -/
theorem bdet_getMember {p tp tps} (mem : Member tp tps) {argTps outTp} :
    BDet p (Builtin.getMember mem) argTps outTp := by
  apply bdet_pure
  intro a a' h1 _
  simp only [List.cons.injEq, Tp.tuple.injEq, and_true] at h1
  exact h1

theorem good_literalArgs {p Γ out} (tp : Tp) (values : List Int) :
    ∀ (k : HList (Tp.denote p) (List.replicate values.length tp) → Expr (Tp.denote p) out),
      (∀ a, Good p Γ (k a)) → Good p Γ (Expr.literalArgs tp values k) := by
  induction values with
  | nil => intro k hk; exact hk _
  | cons x xs ih =>
    intro k hk
    unfold Expr.literalArgs
    exact Good.letIn Good.litNum (fun v => ih _ (fun a => hk _))

theorem good_literalArray {p Γ} {tp : Tp} {n : U 32} {values : List Int} {h} :
    Good p Γ (Expr.literalArray (rep := Tp.denote p) tp n values h) := by
  unfold Expr.literalArray
  exact good_literalArgs tp values _ (fun _ => Good.builtin bdet_mkArray)

/-- One traversal step over an extracted body. Callee lemmas are tried by each proof first. -/
macro "good_step" : tactic => `(tactic| first
  | apply Good.letFn
  | apply Good.letIn
  | (intro _)
  | apply Good.loop
  | apply Good.ite
  | apply Good.skip
  | apply Good.litNum
  | apply Good.constU
  | apply Good.constFp
  | apply Good.var
  | (apply Good.builtin; first
      | exact bdet_readRef | exact bdet_modifyLens _ | exact bdet_arrayIndex | exact bdet_cast
      | exact bdet_fAdd | exact bdet_fMul | exact bdet_fSub | exact bdet_uAdd | exact bdet_uMul
      | exact bdet_uSub | exact bdet_uDiv | exact bdet_ref | exact bdet_writeRef
      | exact bdet_arrayLen | exact bdet_asWitness | exact bdet_uEq | exact bdet_uAnd
      | exact bdet_getMember _ | exact bdet_mkRepeatedArray | exact bdet_mkArray | exact bdet_assert
      | exact bdet_fEq | exact bdet_fNeq | exact bdet_bNot | exact bdet_bNeq | exact bdet_uLt
      | exact bdet_uLeq | exact bdet_uNeq | exact bdet_isUnconstrained | exact bdet_modulusLeBits
      | exact bdet_vectorIndex | exact bdet_makeData))

section
variable {p : Prime}

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem good_to_le_bits32 (hp : 2 ^ 32 < p.natVal) (x : Fp p) :
    Good p Γd («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![x]) := by
  apply Good.call Deposit.HashLookup.to_le_bits_unique
  dsimp only [«std-1.0.0-beta.21::field::to_le_bits»]
  repeat' first
    | (apply Good.builtin; exact bdet_toLeBits32 hp)
    | good_step

theorem good_pow_32 (hp : 2 ^ 32 < p.natVal) (a e : Fp p) :
    Good p Γd («std-1.0.0-beta.21::field::pow_32».call h![] h![a, e]) := by
  apply Good.call Deposit.HashLookup.pow_32_unique
  dsimp only [«std-1.0.0-beta.21::field::pow_32»]
  repeat' first
    | exact good_to_le_bits32 hp _
    | good_step

theorem good_sigma (O : U 32) (x : Tp.denote p (.array .field O)) :
    Good p Γd («poseidon-0.0.0::poseidon::sigma».call h![O] h![x]) := by
  apply Good.call Deposit.HashLookup.sigma_unique
  dsimp only [«poseidon-0.0.0::poseidon::sigma»]
  repeat' good_step

theorem good_apply_matrix (N : U 32) (m : Tp.denote p (.array (.array .field N) N))
    (v : Tp.denote p (.array .field N)) :
    Good p Γd («poseidon-0.0.0::poseidon::apply_matrix».call h![N] h![m, v]) := by
  apply Good.call Deposit.HashLookup.apply_matrix_unique
  dsimp only [«poseidon-0.0.0::poseidon::apply_matrix»]
  repeat' good_step

/-! Call-shape forms: the extracted bodies call these functions as `Expr.call` on a literal
`FuncRef.decl`, where elaboration cannot infer the generics of `FunctionDecl.call`. -/

theorem good_sigma_c (O : U 32) (x : Tp.denote p (.array .field O)) :
    Good p Γd (Expr.call [Tp.field.array O] (Tp.field.array O)
      (FuncRef.decl «poseidon-0.0.0::poseidon::sigma».name [Kind.u 32] h![O]) h![x]) :=
  good_sigma O x

theorem good_apply_matrix_c (N : U 32) (m : Tp.denote p (.array (.array .field N) N))
    (v : Tp.denote p (.array .field N)) :
    Good p Γd (Expr.call [(Tp.field.array N).array N, Tp.field.array N] (Tp.field.array N)
      (FuncRef.decl «poseidon-0.0.0::poseidon::apply_matrix».name [Kind.u 32] h![N]) h![m, v]) :=
  good_apply_matrix N m v

theorem good_config_c (T N X : U 32) (t : Fp p) (rf rp : U 8) (alpha : Fp p)
    (rc : Tp.denote p (.array .field N)) (mds pre : Tp.denote p (.array (.array .field T) T))
    (sparse : Tp.denote p (.array .field X)) :
    Good p Γd (Expr.call
      [Tp.field, Tp.u 8, Tp.u 8, Tp.field, Tp.field.array N, (Tp.field.array T).array T,
        (Tp.field.array T).array T, Tp.field.array X]
      («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X])
      (FuncRef.decl «poseidon-0.0.0::poseidon::config».name [Kind.u 32, Kind.u 32, Kind.u 32] h![T, N, X])
      h![t, rf, rp, alpha, rc, mds, pre, sparse]) :=
  good_config T N X t rf rp alpha rc mds pre sparse

theorem good_permute (hp : 2 ^ 32 < p.natVal) (T N X : U 32)
    (pc : Tp.denote p («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X]))
    (v : Tp.denote p (.array .field T)) :
    Good p Γd («poseidon-0.0.0::poseidon::permute».call h![T, N, X] h![pc, v]) := by
  apply Good.call Deposit.HashLookup.permute_unique
  dsimp only [«poseidon-0.0.0::poseidon::permute»]
  repeat' first
    | exact good_sigma_c _ _
    | exact good_apply_matrix_c _ _ _
    | exact good_pow_32 hp _ _
    | good_step

theorem good_permute_c (hp : 2 ^ 32 < p.natVal) (T N X : U 32)
    (pc : Tp.denote p («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X]))
    (v : Tp.denote p (.array .field T)) :
    Good p Γd (Expr.call [«poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X], Tp.field.array T]
      (Tp.field.array T)
      (FuncRef.decl «poseidon-0.0.0::poseidon::permute».name [Kind.u 32, Kind.u 32, Kind.u 32] h![T, N, X])
      h![pc, v]) :=
  good_permute hp T N X pc v

theorem good_alpha : Good p Γd («poseidon-0.0.0::poseidon::bn254::consts::alpha».call h![] h![]) := by
  apply Good.call Deposit.HashLookup.alpha_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::alpha»]
  repeat' good_step

theorem good_x5_2_config :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::consts::x5_2_config».call h![] h![]) := by
  apply Good.call Deposit.HashLookup.x5_2_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_2_config»]
  repeat' first
    | exact good_literalArray
    | exact good_alpha
    | exact good_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem good_x5_5_config :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::consts::x5_5_config».call h![] h![]) := by
  apply Good.call Deposit.HashLookup.x5_5_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_5_config»]
  repeat' first
    | exact good_literalArray
    | exact good_alpha
    | exact good_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem good_x5_2 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 2)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v]) := by
  apply Good.call Deposit.HashLookup.x5_2_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_2»]
  repeat' first
    | exact good_x5_2_config
    | exact good_permute_c hp _ _ _ _ _
    | good_step

theorem good_x5_5 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 5)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v]) := by
  apply Good.call Deposit.HashLookup.x5_5_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_5»]
  repeat' first
    | exact good_x5_5_config
    | exact good_permute_c hp _ _ _ _ _
    | good_step

theorem good_internal1 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 1)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(1 : U 32), (2 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_2».name [] h![] ]) := by
  apply Good.call Deposit.HashLookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact good_x5_2 hp _
    | good_step

theorem good_internal4 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 4)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(4 : U 32), (5 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_5».name [] h![] ]) := by
  apply Good.call Deposit.HashLookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact good_x5_5 hp _
    | good_step

theorem good_hash_1 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 1)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_1».call h![] h![input]) := by
  apply Good.call Deposit.HashLookup.hash_1_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_1»]
  repeat' first
    | exact good_internal1 hp _
    | good_step

theorem good_hash_4 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 4)) :
    Good p Γd («poseidon-0.0.0::poseidon::bn254::hash_4».call h![] h![input]) := by
  apply Good.call Deposit.HashLookup.hash_4_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_4»]
  repeat' first
    | exact good_internal4 hp _
    | good_step

theorem good_poseidon4 (hp : 2 ^ 32 < p.natVal) (a b c d : Fp p) :
    Good p Γd («deposit-0.0.0::poseidon4».call h![] h![a, b, c, d]) := by
  apply Good.call Deposit.HashLookup.poseidon4_unique
  dsimp only [«deposit-0.0.0::poseidon4»]
  repeat' first
    | exact good_hash_4 hp _
    | good_step

end

#print axioms bdet_getMember
#print axioms good_literalArgs
#print axioms good_literalArray
#print axioms good_to_le_bits32
#print axioms good_pow_32
#print axioms good_sigma
#print axioms good_apply_matrix
#print axioms good_sigma_c
#print axioms good_apply_matrix_c
#print axioms good_config_c
#print axioms good_permute
#print axioms good_permute_c
#print axioms good_alpha
#print axioms good_x5_2_config
#print axioms good_x5_5_config
#print axioms good_x5_2
#print axioms good_x5_5
#print axioms good_internal1
#print axioms good_internal4
#print axioms good_hash_1
#print axioms good_hash_4
#print axioms good_poseidon4
end Determinism
