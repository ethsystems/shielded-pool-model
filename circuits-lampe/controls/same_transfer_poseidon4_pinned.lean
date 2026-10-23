import Transfer.Forward

namespace Controls.Transfer
open Lampe Determinism Transfer.HashGood Transfer.Forward



theorem same_transfer_poseidon4_pinned {st Q} (a b c d : Fp p)
    (h : Omni p Γt st («transfer-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.hash4 a b c d)) :=
  (tgood_poseidon4 Withdraw.Rules.bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

#print axioms same_transfer_poseidon4_pinned
end Controls.Transfer
