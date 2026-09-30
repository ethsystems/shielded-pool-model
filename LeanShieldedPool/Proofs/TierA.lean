import LeanShieldedPool.Statements.L4

namespace LeanShieldedPool

theorem poolSolvency_proof (P : PrimSpec) : poolSolvency P := by
  intro sup txs st hr
  induction hr with
  | empty =>
      intro t
      rfl
  | @step txs st st' tx hr hs ih =>
      intro t
      have hold := ih t
      cases hs with
      | @deposit d hg =>
          change bump st.balance d.note.token d.note.amount t + st.withdrawn t =
            bump st.deposited d.note.token d.note.amount t
          by_cases ht : t = d.note.token
          · simp only [bump, ht, if_true]
            rw [Nat.add_right_comm, ih]
          · simp only [bump, ht, if_false]
            exact hold
      | transfer hg => exact hold
      | @withdraw d hg =>
          change drop st.balance d.note.token d.note.amount t +
            bump st.withdrawn d.note.token d.note.amount t = st.deposited t
          by_cases ht : t = d.note.token
          · subst t
            have hpay := hg.2.2.2.2.2.2
            simp only [drop, bump, ite_true]
            rw [Nat.add_comm (st.withdrawn d.note.token) d.note.amount,
              ← Nat.add_assoc, Nat.sub_add_cancel hpay]
            exact hold
          · simp only [drop, bump, ht, if_false]
            exact hold

theorem noOverWithdrawal_proof (P : PrimSpec) : noOverWithdrawal P := by
  intro sup txs st hr t
  calc
    st.withdrawn t ≤ st.balance t + st.withdrawn t := Nat.le_add_left _ _
    _ = st.deposited t := poolSolvency_proof P sup txs st hr t

end LeanShieldedPool
