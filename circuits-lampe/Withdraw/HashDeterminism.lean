import Determinism.DepositHash
import Withdraw.Lookup
import «withdraw-0.0.0».Extracted

/-!
`Good` proofs in the WITHDRAW environment. The bodies up to `wgood_hash_4` are the
proofs of `Determinism.DepositHash` with the withdraw certificates (`Withdraw.Lookup`) in place of the deposit
ones; the declarations are the same (identical dependency sources). New: the width-3 code
(`x5_3_config`, `x5_3`, `hash_internal<2,3>`, `hash_2`), the three withdraw wrappers, the
Merkle root at the literal `hash_2` reference, and `verify_merkle_proof<32>`.
-/

namespace Withdraw.HashGood
open Lampe Determinism

abbrev Γw := «withdraw-0.0.0».env

section
variable {p : Prime}

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem wgood_to_le_bits32 (hp : 2 ^ 32 < p.natVal) (x : Fp p) :
    Good p Γw («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![x]) := by
  apply Good.call Withdraw.Lookup.to_le_bits_unique
  dsimp only [«std-1.0.0-beta.21::field::to_le_bits»]
  repeat' first
    | (apply Good.builtin; exact bdet_toLeBits32 hp)
    | good_step

theorem wgood_pow_32 (hp : 2 ^ 32 < p.natVal) (a e : Fp p) :
    Good p Γw («std-1.0.0-beta.21::field::pow_32».call h![] h![a, e]) := by
  apply Good.call Withdraw.Lookup.pow_32_unique
  dsimp only [«std-1.0.0-beta.21::field::pow_32»]
  repeat' first
    | exact wgood_to_le_bits32 hp _
    | good_step

theorem wgood_sigma (O : U 32) (x : Tp.denote p (.array .field O)) :
    Good p Γw («poseidon-0.0.0::poseidon::sigma».call h![O] h![x]) := by
  apply Good.call Withdraw.Lookup.sigma_unique
  dsimp only [«poseidon-0.0.0::poseidon::sigma»]
  repeat' good_step

theorem wgood_apply_matrix (N : U 32) (m : Tp.denote p (.array (.array .field N) N))
    (v : Tp.denote p (.array .field N)) :
    Good p Γw («poseidon-0.0.0::poseidon::apply_matrix».call h![N] h![m, v]) := by
  apply Good.call Withdraw.Lookup.apply_matrix_unique
  dsimp only [«poseidon-0.0.0::poseidon::apply_matrix»]
  repeat' good_step


theorem wgood_config_w (T N X : U 32) (t : Fp p) (rf rp : U 8) (alpha : Fp p)
    (rc : Tp.denote p (.array .field N)) (mds pre : Tp.denote p (.array (.array .field T) T))
    (sparse : Tp.denote p (.array .field X)) :
    Good p Γw
      («poseidon-0.0.0::poseidon::config».call h![T, N, X] h![t, rf, rp, alpha, rc, mds, pre, sparse]) := by
  apply Good.call Withdraw.Lookup.config_unique
  dsimp only [«poseidon-0.0.0::poseidon::config»]
  repeat' first
    | apply Good.letFn
    | apply Good.letIn
    | (intro _)
    | apply Good.skip
    | apply Good.litNum
    | apply Good.constU
    | apply Good.var
    | (apply Good.builtin; first
        | exact bdet_cast | exact bdet_assert | exact bdet_fEq | exact bdet_fNeq | exact bdet_uEq
        | exact bdet_uAnd | exact bdet_uAdd | exact bdet_uMul | exact bdet_makeData)

/-! Call-shape forms: the extracted bodies call these functions as `Expr.call` on a literal
`FuncRef.decl`, where elaboration cannot infer the generics of `FunctionDecl.call`. -/

theorem wgood_sigma_c (O : U 32) (x : Tp.denote p (.array .field O)) :
    Good p Γw (Expr.call [Tp.field.array O] (Tp.field.array O)
      (FuncRef.decl «poseidon-0.0.0::poseidon::sigma».name [Kind.u 32] h![O]) h![x]) :=
  wgood_sigma O x

theorem wgood_apply_matrix_c (N : U 32) (m : Tp.denote p (.array (.array .field N) N))
    (v : Tp.denote p (.array .field N)) :
    Good p Γw (Expr.call [(Tp.field.array N).array N, Tp.field.array N] (Tp.field.array N)
      (FuncRef.decl «poseidon-0.0.0::poseidon::apply_matrix».name [Kind.u 32] h![N]) h![m, v]) :=
  wgood_apply_matrix N m v

theorem wgood_config_c (T N X : U 32) (t : Fp p) (rf rp : U 8) (alpha : Fp p)
    (rc : Tp.denote p (.array .field N)) (mds pre : Tp.denote p (.array (.array .field T) T))
    (sparse : Tp.denote p (.array .field X)) :
    Good p Γw (Expr.call
      [Tp.field, Tp.u 8, Tp.u 8, Tp.field, Tp.field.array N, (Tp.field.array T).array T,
        (Tp.field.array T).array T, Tp.field.array X]
      («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X])
      (FuncRef.decl «poseidon-0.0.0::poseidon::config».name [Kind.u 32, Kind.u 32, Kind.u 32] h![T, N, X])
      h![t, rf, rp, alpha, rc, mds, pre, sparse]) :=
  wgood_config_w T N X t rf rp alpha rc mds pre sparse

theorem wgood_permute (hp : 2 ^ 32 < p.natVal) (T N X : U 32)
    (pc : Tp.denote p («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X]))
    (v : Tp.denote p (.array .field T)) :
    Good p Γw («poseidon-0.0.0::poseidon::permute».call h![T, N, X] h![pc, v]) := by
  apply Good.call Withdraw.Lookup.permute_unique
  dsimp only [«poseidon-0.0.0::poseidon::permute»]
  repeat' first
    | exact wgood_sigma_c _ _
    | exact wgood_apply_matrix_c _ _ _
    | exact wgood_pow_32 hp _ _
    | good_step

theorem wgood_permute_c (hp : 2 ^ 32 < p.natVal) (T N X : U 32)
    (pc : Tp.denote p («poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X]))
    (v : Tp.denote p (.array .field T)) :
    Good p Γw (Expr.call [«poseidon-0.0.0::poseidon::PoseidonConfig».tp h![T, N, X], Tp.field.array T]
      (Tp.field.array T)
      (FuncRef.decl «poseidon-0.0.0::poseidon::permute».name [Kind.u 32, Kind.u 32, Kind.u 32] h![T, N, X])
      h![pc, v]) :=
  wgood_permute hp T N X pc v

theorem wgood_alpha : Good p Γw («poseidon-0.0.0::poseidon::bn254::consts::alpha».call h![] h![]) := by
  apply Good.call Withdraw.Lookup.alpha_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::alpha»]
  repeat' good_step

theorem wgood_x5_2_config :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::consts::x5_2_config».call h![] h![]) := by
  apply Good.call Withdraw.Lookup.x5_2_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_2_config»]
  repeat' first
    | exact good_literalArray
    | exact wgood_alpha
    | exact wgood_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem wgood_x5_5_config :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::consts::x5_5_config».call h![] h![]) := by
  apply Good.call Withdraw.Lookup.x5_5_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_5_config»]
  repeat' first
    | exact good_literalArray
    | exact wgood_alpha
    | exact wgood_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem wgood_x5_2 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 2)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v]) := by
  apply Good.call Withdraw.Lookup.x5_2_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_2»]
  repeat' first
    | exact wgood_x5_2_config
    | exact wgood_permute_c hp _ _ _ _ _
    | good_step

theorem wgood_x5_5 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 5)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v]) := by
  apply Good.call Withdraw.Lookup.x5_5_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_5»]
  repeat' first
    | exact wgood_x5_5_config
    | exact wgood_permute_c hp _ _ _ _ _
    | good_step

theorem wgood_internal1 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 1)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(1 : U 32), (2 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_2».name [] h![] ]) := by
  apply Good.call Withdraw.Lookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact wgood_x5_2 hp _
    | good_step

theorem wgood_internal4 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 4)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(4 : U 32), (5 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_5».name [] h![] ]) := by
  apply Good.call Withdraw.Lookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact wgood_x5_5 hp _
    | good_step

theorem wgood_hash_1 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 1)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_1».call h![] h![input]) := by
  apply Good.call Withdraw.Lookup.hash_1_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_1»]
  repeat' first
    | exact wgood_internal1 hp _
    | good_step

theorem wgood_hash_4 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 4)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_4».call h![] h![input]) := by
  apply Good.call Withdraw.Lookup.hash_4_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_4»]
  repeat' first
    | exact wgood_internal4 hp _
    | good_step


theorem wgood_x5_3_config :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».call h![] h![]) := by
  apply Good.call Withdraw.Lookup.x5_3_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_3_config»]
  repeat' first
    | exact good_literalArray
    | exact wgood_alpha
    | exact wgood_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step

theorem wgood_x5_3 (hp : 2 ^ 32 < p.natVal) (v : Tp.denote p (.array .field 3)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v]) := by
  apply Good.call Withdraw.Lookup.x5_3_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_3»]
  repeat' first
    | exact wgood_x5_3_config
    | exact wgood_permute_c hp _ _ _ _ _
    | good_step

theorem wgood_internal2 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 2)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(2 : U 32), (3 : U 32)]
      h![input, FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name [] h![] ]) := by
  apply Good.call Withdraw.Lookup.hash_internal_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | exact wgood_x5_3 hp _
    | good_step

theorem wgood_hash_2 (hp : 2 ^ 32 < p.natVal) (input : Tp.denote p (.array .field 2)) :
    Good p Γw («poseidon-0.0.0::poseidon::bn254::hash_2».call h![] h![input]) := by
  apply Good.call Withdraw.Lookup.hash_2_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_2»]
  repeat' first
    | exact wgood_internal2 hp _
    | good_step

theorem wgood_poseidon1 (hp : 2 ^ 32 < p.natVal) (a : Fp p) :
    Good p Γw («withdraw-0.0.0::poseidon1».call h![] h![a]) := by
  apply Good.call Withdraw.Lookup.poseidon1_unique
  dsimp only [«withdraw-0.0.0::poseidon1»]
  repeat' first
    | exact wgood_hash_1 hp _
    | good_step

theorem wgood_poseidon2 (hp : 2 ^ 32 < p.natVal) (a b : Fp p) :
    Good p Γw («withdraw-0.0.0::poseidon2».call h![] h![a, b]) := by
  apply Good.call Withdraw.Lookup.poseidon2_unique
  dsimp only [«withdraw-0.0.0::poseidon2»]
  repeat' first
    | exact wgood_hash_2 hp _
    | good_step

theorem wgood_poseidon4 (hp : 2 ^ 32 < p.natVal) (a b c d : Fp p) :
    Good p Γw («withdraw-0.0.0::poseidon4».call h![] h![a, b, c, d]) := by
  apply Good.call Withdraw.Lookup.poseidon4_unique
  dsimp only [«withdraw-0.0.0::poseidon4»]
  repeat' first
    | exact wgood_hash_4 hp _
    | good_step

theorem wgood_bmr (hp : 2 ^ 32 < p.natVal) (leaf : Fp p) (depth : U 32)
    (indices : Tp.denote p (.array .bool 32)) (siblings : Tp.denote p (.array .field 32)) :
    Good p Γw («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
      h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![], leaf, depth, indices, siblings]) := by
  apply Good.call Withdraw.Lookup.bmr_unique
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  repeat' first
    | exact wgood_hash_2 hp _
    | (apply Good.builtin; exact bdet_uLt)
    | good_step

theorem wgood_vmp (hp : 2 ^ 32 < p.natVal) (leaf root : Fp p) (depth : U 32)
    (indices : Tp.denote p (.array .bool 32)) (siblings : Tp.denote p (.array .field 32)) :
    Good p Γw («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)] h![leaf, root, depth, indices, siblings]) := by
  apply Good.call Withdraw.Lookup.vmp_unique
  dsimp only [«withdraw-0.0.0::verify_merkle_proof»]
  repeat' first
    | exact wgood_bmr hp _ _ _ _
    | good_step
end

#print axioms wgood_to_le_bits32
#print axioms wgood_pow_32
#print axioms wgood_sigma
#print axioms wgood_apply_matrix
#print axioms wgood_config_w
#print axioms wgood_sigma_c
#print axioms wgood_apply_matrix_c
#print axioms wgood_config_c
#print axioms wgood_permute
#print axioms wgood_permute_c
#print axioms wgood_alpha
#print axioms wgood_x5_2_config
#print axioms wgood_x5_5_config
#print axioms wgood_x5_2
#print axioms wgood_x5_5
#print axioms wgood_internal1
#print axioms wgood_internal4
#print axioms wgood_hash_1
#print axioms wgood_hash_4
#print axioms wgood_x5_3_config
#print axioms wgood_x5_3
#print axioms wgood_internal2
#print axioms wgood_hash_2
#print axioms wgood_poseidon1
#print axioms wgood_poseidon2
#print axioms wgood_poseidon4
#print axioms wgood_bmr
#print axioms wgood_vmp
end Withdraw.HashGood
