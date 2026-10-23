import Determinism.DepositHash
/-! Must-fail control: `config_det` restated for a call with no uniqueness certificate
(`consts::x5_3_config`), proved as `good_x5_2_config` is, with the nearest certificate. -/
namespace Controls.DepositHash
open Lampe Determinism
set_option backward.isDefEq.respectTransparency false
theorem config_det_without_certificate {p} :
    Inter p Γd («poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».call h![] h![]) := by
  apply Good.inter
  apply Good.call Deposit.HashLookup.x5_2_config_unique
  dsimp only [«poseidon-0.0.0::poseidon::bn254::consts::x5_3_config»]
  repeat' first
    | exact good_literalArray
    | exact good_alpha
    | exact good_config_c _ _ _ _ _ _ _ _ _ _ _
    | good_step
end Controls.DepositHash
