-- EXPECT: unsolved goals
-- Negative control for `balanceIsLiveValue_proof`.
-- Same minting transfer as neg_l4_nominting (first-input membership
-- dropped): the contract balance stays 5 while live value becomes 12.
-- The proof attempt below must not close.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4BalanceLive

open NonVacuity

abbrev tMint : TransferData Toy :=
  { key := ()
    in1 := ⟨(), 7, (), 9⟩
    in2 := ⟨(), 0, (), 1⟩
    out1 := ⟨(), 4, (), 11⟩
    out2 := ⟨(), 3, (), 20⟩
    snapshot := 1 }

/-- FALSE: it reads 5 = 12. The control passes only if this proof fails. -/
example :
    (tMint.post (d0.post st0)).balance () = liveValue (tMint.post (d0.post st0)) () := by
  norm_num [TransferData.post, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump]

end NegL4BalanceLive
end LeanShieldedPool
