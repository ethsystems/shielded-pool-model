import Balance.Basic
import Refinement.PathLocal

/-!
# Token balances on the path-local premises

`refineB_run` and `refineB_w9` (`Balance/Basic.lean`) take the global tree premises
`TreeLink` and `TreeHyp` of `refineP_run`. The two theorems here are the same statements with those two premises
replaced by the path-local `PathFacts` and `PathTreeHyp`, through `refinePL_run`. The token
premises and the conclusions are unchanged.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-- **`refineB_run` on the per-path premises.** Every premise of `refinePL_run`, plus the token
premises of `refineB_run`: the external pool balance equals the model's balance field and the
live note value in every accepted history. -/
theorem refineBPL_run {H : Nat → Nat → Nat} {X : Contract} {K : Chain} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    (hinjT : Function.Injective E.tok) (hRd : PoolCallReadings X)
    (hz : PoolStartsEmpty X K) (hND : NoOutsideDebit X K) (hNC : NoOutsideCredit X K)
    (hTR : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hacc : AcceptedB X K h σ w)
    (hC1 : NoSetVerifier h) (hS : NoSelfWithdraw X h) (hEx : ExtractedWitnesses C ext h)
    (hPT : PathTreeHyp H (ghostLeaves h) (checkedInputs E ext pext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      (∀ t, K.bal w (E.tok t) X.self = st.balance t) ∧
      (∀ t, K.bal w (E.tok t) X.self = liveValue st t) := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refinePL_run hG0 hRB hEnv hD hTP hWP hA hC hPF hinj hacc.accepted hC1 hEx hPT hcr
  have hTC := TokenCallFacts.of_posts hD hTP hWP hRd
  have hbal : ∀ t, K.bal w (E.tok t) X.self = st.balance t := fun t => by
    rw [bal_eq_ledger hTC hz hND hNC hTR hacc hC1 hS, hr.balance_eq, ← modelBal_eraseSnap txs t,
      hE, modelBal_txsOf hC hinjT hEx t]
  refine ⟨txs, st, hE, hr, hR, hbal, fun t => ?_⟩
  rw [hbal t,
    balanceIsLiveValue_prov _ txs st hr (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr)) t]

/-- **`refineB_w9` on the per-path premises.** Every premise of `refinePL_run`, plus the call
readings, the injective token encoding, no outside debit and rollback: the model's balance field,
its live note value, every amount the withdrawal guard admits and every amount
`withdraw_balanceP` bounds are at most the pool's external balance. -/
theorem refineBPL_w9 {H : Nat → Nat → Nat} {X : Contract} {K : Chain} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    (hinjT : Function.Injective E.tok) (hRd : PoolCallReadings X)
    (hND : NoOutsideDebit X K) (hTR : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hacc : AcceptedB X K h σ w)
    (hC1 : NoSetVerifier h) (hEx : ExtractedWitnesses C ext h)
    (hPT : PathTreeHyp H (ghostLeaves h) (checkedInputs E ext pext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      (∀ t, st.balance t ≤ K.bal w (E.tok t) X.self) ∧
      (∀ t, liveValue st t ≤ K.bal w (E.tok t) X.self) ∧
      (∀ d : WithdrawData P, withdrawGuard' d st →
        d.note.amount ≤ K.bal w (E.tok d.note.token) X.self) ∧
      (∀ d : WithdrawData P, CryptoHyp P (txs ++ [.withdraw d]) → d.note.cm ∈ st.leaves →
        d.note.ownedBy d.key → st.fresh d.nf → d.note.wf →
        d.note.amount ≤ K.bal w (E.tok d.note.token) X.self) := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refinePL_run hG0 hRB hEnv hD hTP hWP hA hC hPF hinj hacc.accepted hC1 hEx hPT hcr
  have hTC := TokenCallFacts.of_posts hD hTP hWP hRd
  have hbal : ∀ t, st.balance t ≤ K.bal w (E.tok t) X.self := fun t => by
    rw [hr.balance_eq, ← modelBal_eraseSnap txs t, hE, modelBal_txsOf hC hinjT hEx t]
    exact ledger_le_bal hTC hND hTR hacc hC1 (E.tok t)
  have hcr' : CryptoHyp P txs := cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr)
  refine ⟨txs, st, hE, hr, hR, hbal, fun t => ?_, fun d hg => ?_,
    fun d hc hin ho hf hwf => ?_⟩
  · rw [← balanceIsLiveValue_prov _ txs st hr hcr' t]
    exact hbal t
  · exact Nat.le_trans hg.2.2.2.2.2.2 (hbal _)
  · exact Nat.le_trans (withdraw_balanceP hr d hc hin ho hf hwf) (hbal _)

end LeanShieldedPool.Refine
