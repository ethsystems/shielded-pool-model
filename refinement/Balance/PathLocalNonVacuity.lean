import Balance.PathLocal
import Balance.ToyRun
import Refinement.PathLocalNonVacuity

/-!
# Token balances on the path-local premises: every premise instantiated

`refineBPL_run` and `refineBPL_w9` on the toy history (`ToyRun`) with the honest chain
`BalanceToy.KH`: the token premises and chain run from `BalanceToyRun`, the per-path premises
`PathToy.hPF` and `PathToy.hPT` from `Refinement/PathLocalNonVacuity.lean` (the real LeanIMT
fold of `Tree/LeanImt.lean`, depth-2 withdrawal path). The instance shows the premises are jointly
satisfiable; it says nothing about the deployed pool or any real token.
-/

namespace LeanShieldedPool.Refine.BalancePathToy

open LeanShieldedPool LeanShieldedPool.Refine

/-- **Non-vacuity of `refineBPL_run`.** Every premise holds on the toy history; the external
pool balance equals the model's balance field and the live note value. -/
theorem refineBPL_run_toy : ∃ txs st, txs.map eraseSnap = txsOf ToyRun.ext ToyRun.hist ∧
    Run' (supOf Toy.E ToyRun.hist) txs st ∧
    RepP Toy.H Toy.E (supOf Toy.E ToyRun.hist) (ghostLeaves ToyRun.hist) ToyRun.σ3 st ∧
    (∀ t, BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok t) ToyRun.X.self = st.balance t) ∧
    (∀ t, BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok t) ToyRun.X.self = liveValue st t) :=
  refineBPL_run ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hC PathToy.hPF ToyRun.hinj
    BalanceToyRun.hinjT BalanceToyRun.hRd (BalanceToy.kh_startX ToyRun.X rfl) (BalanceToy.kh_nodX ToyRun.X rfl) (BalanceToy.kh_nocX ToyRun.X rfl)
    (BalanceToy.kh_rbX ToyRun.X) BalanceToyRun.accN ToyRun.hC1 BalanceToyRun.sN ToyRun.hEx PathToy.hPT ToyRun.hcr

/-- **Non-vacuity of `refineBPL_w9`.** Every premise holds on the toy history. -/
theorem refineBPL_w9_toy : ∃ txs st, txs.map eraseSnap = txsOf ToyRun.ext ToyRun.hist ∧
    Run' (supOf Toy.E ToyRun.hist) txs st ∧
    RepP Toy.H Toy.E (supOf Toy.E ToyRun.hist) (ghostLeaves ToyRun.hist) ToyRun.σ3 st ∧
    (∀ t, st.balance t ≤ BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok t) ToyRun.X.self) ∧
    (∀ t, liveValue st t ≤ BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok t) ToyRun.X.self) ∧
    (∀ d : WithdrawData Toy.P, withdrawGuard' d st →
      d.note.amount ≤ BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok d.note.token) ToyRun.X.self) ∧
    (∀ d : WithdrawData Toy.P, CryptoHyp Toy.P (txs ++ [.withdraw d]) → d.note.cm ∈ st.leaves →
      d.note.ownedBy d.key → st.fresh d.nf → d.note.wf →
      d.note.amount ≤ BalanceToy.KH.bal BalanceToyRun.w3 (Toy.E.tok d.note.token) ToyRun.X.self) :=
  refineBPL_w9 ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hC PathToy.hPF ToyRun.hinj
    BalanceToyRun.hinjT BalanceToyRun.hRd (BalanceToy.kh_nodX ToyRun.X rfl) (BalanceToy.kh_rbX ToyRun.X) BalanceToyRun.accN ToyRun.hC1 ToyRun.hEx
    PathToy.hPT ToyRun.hcr

end LeanShieldedPool.Refine.BalancePathToy
