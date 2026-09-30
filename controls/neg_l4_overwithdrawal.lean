-- EXPECT: unsolved goals
-- Negative control for `noOverWithdrawal_proof`.
-- Same weakened withdraw guard as neg_l4_solvency (membership and solvency
-- conjuncts removed): after a 5-unit deposit and an accepted 7-unit
-- withdrawal, total withdrawn (7) exceeds total deposited (5). The proof
-- attempt below must not close.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4OverWithdrawal

open NonVacuity

abbrev nBig : Note Toy := ⟨(), 7, (), 9⟩
abbrev wBig : WithdrawData Toy := ⟨(), nBig, (), 1⟩

/-- FALSE: it reads 7 ≤ 5. The control passes only if this proof fails. -/
example :
    (wBig.post (d0.post st0)).withdrawn () ≤ (wBig.post (d0.post st0)).deposited () := by
  norm_num [WithdrawData.post, DepositData.post, St.empty, bump]

end NegL4OverWithdrawal
end LeanShieldedPool
