import Determinism.DepositHash
/-! Must-fail control: the `to_le_bits<32>` traversal without `2^32 < p`, so without
`bdet_toLeBits32`: the toLeBits builtin has no determinism lemma. -/
namespace Controls.DepositHash
open Lampe Determinism
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
theorem to_le_bits_good_without_bound {p : Prime} (x : Fp p) :
    Good p Γd («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![x]) := by
  apply Good.call Deposit.HashLookup.to_le_bits_unique
  dsimp only [«std-1.0.0-beta.21::field::to_le_bits»]
  repeat' first
    | good_step
end Controls.DepositHash
