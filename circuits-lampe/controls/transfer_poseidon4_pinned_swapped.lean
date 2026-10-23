import Transfer.Forward

namespace Controls.Transfer
open Lampe Determinism Transfer.HashGood Transfer.Forward



theorem transfer_poseidon4_pinned_swapped {st Q} (a b c d : Fp p)
    (h : Omni p Γt st («transfer-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.hash4 b a c d)) :=
  (tgood_poseidon4 Withdraw.Rules.bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

#print axioms transfer_poseidon4_pinned_swapped
end Controls.Transfer
