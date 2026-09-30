import LeanShieldedPool.Proofs.TierA
import LeanShieldedPool.Proofs.Conservation

namespace LeanShieldedPool

theorem noMinting_proof (P : PrimSpec) : noMinting P := by
  intro sup txs st hr hc t
  calc
    liveValue st t ≤ st.withdrawn t + liveValue st t := Nat.le_add_left _ _
    _ = st.deposited t := (valueConservation_proof P sup txs st hr hc t).symm

theorem balanceIsLiveValue_proof (P : PrimSpec) : balanceIsLiveValue P := by
  intro sup txs st hr hc t
  apply Nat.add_right_cancel (m := st.withdrawn t)
  calc
    st.balance t + st.withdrawn t = st.deposited t :=
      poolSolvency_proof P sup txs st hr t
    _ = st.withdrawn t + liveValue st t := valueConservation_proof P sup txs st hr hc t
    _ = liveValue st t + st.withdrawn t := Nat.add_comm _ _

end LeanShieldedPool
