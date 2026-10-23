import Determinism
import Deposit.ConfigLookup

/-!
The determinism framework applied to one extracted function, `poseidon::config`
(asserts, integer and field comparisons, casts, `makeData`). Every two accepting derivations of a
`config` call share an outcome.
-/

namespace Determinism
open Lampe

theorem bdet_assert {p argTps outTp} : BDet p Builtin.assert argTps outTp := bdet_pure inj_unit
theorem bdet_fEq {p argTps outTp} : BDet p Builtin.fEq argTps outTp := bdet_pure inj_unit
theorem bdet_fNeq {p argTps outTp} : BDet p Builtin.fNeq argTps outTp := bdet_pure inj_unit
theorem bdet_uEq {p argTps outTp} : BDet p Builtin.uEq argTps outTp :=
  bdet_pure (inj_width_arg (fun _ => ⟨_, rfl⟩))
theorem bdet_uAnd {p argTps outTp} : BDet p Builtin.uAnd argTps outTp :=
  bdet_pure (inj_width_out (fun _ => rfl))
theorem bdet_uAdd {p argTps outTp} : BDet p Builtin.uAdd argTps outTp :=
  bdet_pure (inj_width_out (fun _ => rfl))
theorem bdet_uMul {p argTps outTp} : BDet p Builtin.uMul argTps outTp :=
  bdet_pure (inj_width_out (fun _ => rfl))
theorem bdet_makeData {p argTps outTp} : BDet p Builtin.makeData argTps outTp := by
  apply bdet_pure
  rintro ⟨n, f⟩ ⟨n', f'⟩ _ h2
  simp only [Tp.tuple.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

set_option maxHeartbeats 2000000 in
theorem good_config {p} (T N X : U 32) (t : Fp p) (rf rp : U 8) (alpha : Fp p)
    (rc : Tp.denote p (.array .field N)) (mds pre : Tp.denote p (.array (.array .field T) T))
    (sparse : Tp.denote p (.array .field X)) :
    Good p «deposit-0.0.0».env
      («poseidon-0.0.0::poseidon::config».call h![T, N, X] h![t, rf, rp, alpha, rc, mds, pre, sparse]) := by
  apply Good.call Deposit.ConfigLookup.config_unique
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

theorem config_det {p} (T N X : U 32) (t : Fp p) (rf rp : U 8) (alpha : Fp p)
    (rc : Tp.denote p (.array .field N)) (mds pre : Tp.denote p (.array (.array .field T) T))
    (sparse : Tp.denote p (.array .field X)) :
    Inter p «deposit-0.0.0».env
      («poseidon-0.0.0::poseidon::config».call h![T, N, X] h![t, rf, rp, alpha, rc, mds, pre, sparse]) :=
  (good_config T N X t rf rp alpha rc mds pre sparse).inter

#print axioms bdet_assert
#print axioms bdet_fEq
#print axioms bdet_fNeq
#print axioms bdet_uEq
#print axioms bdet_uAnd
#print axioms bdet_uAdd
#print axioms bdet_uMul
#print axioms bdet_makeData
#print axioms good_config
#print axioms config_det
end Determinism
