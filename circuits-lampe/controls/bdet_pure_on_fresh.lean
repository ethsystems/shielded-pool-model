import Determinism.DepositHash
/-! Must-fail control: `bdet_pure` applied to `Builtin.fresh`, whose outcome is not
unique (any value). -/
namespace Controls.DepositHash
open Lampe Determinism
theorem bdet_pure_on_fresh {p argTps outTp} : BDet p Builtin.fresh argTps outTp := bdet_pure inj_unit
end Controls.DepositHash
