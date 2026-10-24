-- Control (must fail to compile): the accounting equation `bal_eq_ledger` with `TokenRollback`
-- dropped. A reverted pool call whose token pull is not rolled back leaves the pool's external
-- balance above the calldata ledger (`BalanceToy.no_rollback_breaks_eq`; the general statement
-- without the premise is refuted by `BalanceToy.eq_needs_rollback`), so the equation does not
-- follow. Every other premise is supplied; the one goal left open is `TokenRollback X K`.
import Balance.Basic

namespace LeanShieldedPool.Refine

example {X : Contract} {K : Chain} (hTC : TokenCallFacts X)
    (hz : PoolStartsEmpty X K) (hND : NoOutsideDebit X K) (hNC : NoOutsideCredit X K)
    {h : List Call} {σ : Storage} {w : K.World}
    (hb : AcceptedB X K h σ w) (hC1 : NoSetVerifier h) (hS : NoSelfWithdraw X h) (t : Nat) :
    K.bal w t X.self = ledger h t := by
  refine bal_eq_ledger hTC hz hND hNC ?_ hb hC1 hS t

end LeanShieldedPool.Refine
