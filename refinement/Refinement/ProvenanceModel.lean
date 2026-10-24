import Refinement.Cases

/-!
# Root provenance, part 2: the model variant `Step'`

`Step'` is `Step` (`Pool/Tx.lean`) with one change: in the transfer and withdraw guards the root
conjunct `st.rootInWindow d.snapshot` (the snapshot is one of the last 100 recorded leaf counts)
becomes provenance, `d.snapshot ≤ st.minted.length` (the snapshot is a leaf count of the current
tree). Every other conjunct and every post-state is unchanged (`transfer_guard_iff`,
`withdraw_guard_iff`).

`Run'.to_run`: every `Step'` run is matched by a `Step` run through the same states whose
operations agree up to snapshots (`eraseSnap`). The snapshot moves to the current leaf count,
which is always in the window (`Run'.length_mem_window`), and membership at an earlier prefix
implies membership at the current one. The six money theorems then hold for `Step'` by the
existing proofs (`*_prov`); no money lemma breaks.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-- The transfer guard without its root conjunct (the other 18 conjuncts, unchanged). -/
def transferRest (d : TransferData P) (st : St P) : Prop :=
  d.in1.ownedBy d.key ∧
  d.in2.ownedBy d.key ∧
  st.inTreeAt d.snapshot d.in1.cm ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  st.fresh d.nf1 ∧
  st.fresh d.nf2 ∧
  d.nf1 ≠ d.nf2 ∧
  d.in2.token = d.in1.token ∧
  d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  U128 d.in1.amount ∧
  U128 d.in2.amount ∧
  U128 d.out1.amount ∧
  U128 d.out2.amount ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount ∧
  d.out1.cm ∉ st.leaves ∧
  d.out2.cm ∉ st.leaves ∧
  d.out1.cm ≠ d.out2.cm

/-- The withdraw guard without its root conjunct (the other 6 conjuncts, unchanged). -/
def withdrawRest (d : WithdrawData P) (st : St P) : Prop :=
  st.inTreeAt d.snapshot d.note.cm ∧
  d.note.ownedBy d.key ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount ∧
  d.note.amount ≤ st.balance d.note.token

/-- The existing transfer guard is the window conjunct and the rest. -/
theorem transfer_guard_iff (d : TransferData P) (st : St P) :
    d.guard st ↔ st.rootInWindow d.snapshot ∧ transferRest d st := Iff.rfl

theorem withdraw_guard_iff (d : WithdrawData P) (st : St P) :
    d.guard st ↔ st.rootInWindow d.snapshot ∧ withdrawRest d st := Iff.rfl

/-- **Provenance transfer guard**: the snapshot is a leaf count of the current tree. -/
def transferGuard' (d : TransferData P) (st : St P) : Prop :=
  d.snapshot ≤ st.minted.length ∧ transferRest d st

/-- **Provenance withdraw guard.** -/
def withdrawGuard' (d : WithdrawData P) (st : St P) : Prop :=
  d.snapshot ≤ st.minted.length ∧ withdrawRest d st

/-- `Step` with the provenance root conjunct. Post-states are those of `Step`. -/
inductive Step' : St P → Tx P → St P → Prop where
  | deposit {st : St P} {d : DepositData P} :
      d.guard st → Step' st (.deposit d) (d.post st)
  | transfer {st : St P} {d : TransferData P} :
      transferGuard' d st → Step' st (.transfer d) (d.post st)
  | withdraw {st : St P} {d : WithdrawData P} :
      withdrawGuard' d st → Step' st (.withdraw d) (d.post st)

inductive Run' (sup : P.Token → Prop) : List (Tx P) → St P → Prop where
  | empty : Run' sup [] (St.empty P sup)
  | step {txs : List (Tx P)} {st st' : St P} {tx : Tx P} :
      Run' sup txs st → Step' st tx st' → Run' sup (txs ++ [tx]) st'

/-- `Step'` accepts everything `Step` accepts: the window entries are leaf counts. -/
theorem step_to_step' {st st' : St P} {tx : Tx P} (hw : ∀ n ∈ st.window, n ≤ st.minted.length)
    (h : Step st tx st') : Step' st tx st' := by
  cases h with
  | deposit hg => exact Step'.deposit hg
  | transfer hg => exact Step'.transfer ⟨hw _ hg.1, hg.2⟩
  | withdraw hg => exact Step'.withdraw ⟨hw _ hg.1, hg.2⟩

theorem mem_pushWindow_self (w : List Nat) (n : Nat) : n ∈ St.pushWindow w n := by
  unfold St.pushWindow rootWindow
  exact List.mem_cons_self

/-- In every `Step'` run the current leaf count is in the window. -/
theorem Run'.length_mem_window {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (h : Run' sup txs st) : st.minted.length ∈ st.window := by
  induction h with
  | empty => exact List.mem_singleton_self 0
  | @step txs st st' tx hr hs ih =>
    cases hs with
    | @deposit d hg =>
      show (st.minted ++ [d.note]).length ∈ St.pushWindow st.window (st.minted.length + 1)
      rw [List.length_append, List.length_singleton]
      exact mem_pushWindow_self _ _
    | @transfer d hg =>
      show (st.minted ++ [d.out1, d.out2]).length ∈ St.pushWindow st.window (st.minted.length + 2)
      rw [List.length_append]
      exact mem_pushWindow_self _ _
    | withdraw hg => exact ih

theorem st_leaves_length (st : St P) : st.leaves.length = st.minted.length := List.length_map _

theorem inTreeAt_current {st : St P} {n : Nat} {c : P.Commitment} (h : st.inTreeAt n c) :
    st.inTreeAt st.minted.length c := by
  unfold St.inTreeAt at h ⊢
  rw [← st_leaves_length, List.take_length]
  exact List.mem_of_mem_take h

/-- **Simulation.** Every `Step'` run is matched by a `Step` run with the same final state and
the same operations up to snapshots. -/
theorem Run'.to_run {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P} (h : Run' sup txs st) :
    ∃ txs₀, Run sup txs₀ st ∧ txs₀.map eraseSnap = txs.map eraseSnap := by
  induction h with
  | empty => exact ⟨[], Run.empty, rfl⟩
  | @step txs st st' tx hr hs ih =>
    obtain ⟨txs₀, hr₀, he⟩ := ih
    have hwin := hr.length_mem_window
    cases hs with
    | @deposit d hg =>
      refine ⟨txs₀ ++ [.deposit d], Run.step hr₀ (Step.deposit hg), ?_⟩
      rw [List.map_append, List.map_append, he]
    | @transfer d hg =>
      obtain ⟨-, ho1, ho2, hm1, hm2, hrest⟩ := hg
      let d₀ : TransferData P := { d with snapshot := st.minted.length }
      have hg₀ : d₀.guard st :=
        ⟨hwin, ho1, ho2, inTreeAt_current hm1, hm2.imp_right inTreeAt_current, hrest⟩
      refine ⟨txs₀ ++ [.transfer d₀], Run.step hr₀ (Step.transfer hg₀), ?_⟩
      rw [List.map_append, List.map_append, he]
      rfl
    | @withdraw d hg =>
      obtain ⟨-, hm, hrest⟩ := hg
      let d₀ : WithdrawData P := { d with snapshot := st.minted.length }
      have hg₀ : d₀.guard st := ⟨hwin, inTreeAt_current hm, hrest⟩
      refine ⟨txs₀ ++ [.withdraw d₀], Run.step hr₀ (Step.withdraw hg₀), ?_⟩
      rw [List.map_append, List.map_append, he]
      rfl

/-- In every `Step` run the window entries are leaf counts of the current tree. -/
theorem run_window_le {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P} (h : Run sup txs st) :
    ∀ n ∈ st.window, n ≤ st.minted.length := by
  induction h with
  | empty =>
    intro n hn
    rw [List.mem_singleton.1 hn]
    exact Nat.le_refl 0
  | @step txs st st' tx hr hs ih =>
    intro n hn
    cases hs with
    | @deposit d hg =>
      have hn' : n ∈ (st.minted.length + 1) :: st.window := List.mem_of_mem_take hn
      show n ≤ (st.minted ++ [d.note]).length
      rw [List.length_append, List.length_singleton]
      rcases List.mem_cons.1 hn' with rfl | h'
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le (ih n h')
    | @transfer d hg =>
      have hn' : n ∈ (st.minted.length + 2) :: st.window := List.mem_of_mem_take hn
      show n ≤ (st.minted ++ [d.out1, d.out2]).length
      rw [List.length_append]
      rcases List.mem_cons.1 hn' with rfl | h'
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih n h') (Nat.le_add_right _ _)
    | withdraw hg => exact ih n hn

/-- Every `Step` run is a `Step'` run: `Step'` only weakens the root conjunct. -/
theorem run_to_run' {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P} (h : Run sup txs st) :
    Run' sup txs st := by
  induction h with
  | empty => exact Run'.empty
  | @step txs st st' tx hr hs ih => exact Run'.step ih (step_to_step' (run_window_le hr) hs)

/-! ## The money theorems for `Step'` -/

theorem flatMap_eraseSnap {β : Type} (f : Tx P → List β) (hf : ∀ tx, f (eraseSnap tx) = f tx)
    (txs : List (Tx P)) : (txs.map eraseSnap).flatMap f = txs.flatMap f := by
  induction txs with
  | nil => rfl
  | cons tx txs ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, hf, ih]

theorem spends_eraseSnap (tx : Tx P) : (eraseSnap tx).spends = tx.spends := by cases tx <;> rfl

theorem consumes_eraseSnap (tx : Tx P) : (eraseSnap tx).consumes = tx.consumes := by
  cases tx <;> rfl

theorem flatMap_eq_of_eraseSnap {β : Type} (f : Tx P → List β) (hf : ∀ tx, f (eraseSnap tx) = f tx)
    {txs₀ txs : List (Tx P)} (he : txs₀.map eraseSnap = txs.map eraseSnap) :
    txs₀.flatMap f = txs.flatMap f := by
  rw [← flatMap_eraseSnap f hf txs₀, he, flatMap_eraseSnap f hf txs]

theorem cryptoHyp_of_eraseSnap_eq {txs₀ txs : List (Tx P)}
    (he : txs₀.map eraseSnap = txs.map eraseSnap) (hc : CryptoHyp P txs) : CryptoHyp P txs₀ := by
  have hn : runNotes txs₀ = runNotes txs := by
    rw [← runNotes_eraseSnap txs₀, he, runNotes_eraseSnap]
  have hk : runKeys txs₀ = runKeys txs := by
    rw [← runKeys_eraseSnap txs₀, he, runKeys_eraseSnap]
  exact ⟨fun n h1 n' h2 => hc.commit_inj n (hn ▸ h1) n' (hn ▸ h2),
    fun k h1 k' h2 => hc.derivePub_inj k (hk ▸ h1) k' (hk ▸ h2)⟩

/-- Pool solvency for `Step'`. -/
theorem poolSolvency_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (t : P.Token) : st.balance t + st.withdrawn t = st.deposited t := by
  obtain ⟨txs₀, h₀, -⟩ := h.to_run
  exact poolSolvency_proof P sup txs₀ st h₀ t

/-- No over-withdrawal for `Step'`. -/
theorem noOverWithdrawal_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (t : P.Token) : st.withdrawn t ≤ st.deposited t := by
  obtain ⟨txs₀, h₀, -⟩ := h.to_run
  exact noOverWithdrawal_proof P sup txs₀ st h₀ t

/-- Nullifier uniqueness for `Step'`. -/
theorem nullifierUniqueness_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) : (txs.flatMap Tx.spends).Nodup := by
  obtain ⟨txs₀, h₀, he⟩ := h.to_run
  rw [← flatMap_eq_of_eraseSnap Tx.spends spends_eraseSnap he]
  exact nullifierUniqueness_proof P sup txs₀ st h₀

/-- No double spend (L3 theorem 1) for `Step'`. -/
theorem noDoubleSpend_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (hc : CryptoHyp P txs) : noteSpentAtMostOnce txs := by
  obtain ⟨txs₀, h₀, he⟩ := h.to_run
  have h1 := noDoubleSpend_proof P sup txs₀ st h₀ (cryptoHyp_of_eraseSnap_eq he hc)
  unfold noteSpentAtMostOnce spentCommitments at h1 ⊢
  rwa [← flatMap_eq_of_eraseSnap Tx.consumes consumes_eraseSnap he]

/-- Value conservation (L3 theorem 2) for `Step'`. -/
theorem valueConservation_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (hc : CryptoHyp P txs) (t : P.Token) :
    st.deposited t = st.withdrawn t + liveValue st t := by
  obtain ⟨txs₀, h₀, he⟩ := h.to_run
  exact valueConservation_proof P sup txs₀ st h₀ (cryptoHyp_of_eraseSnap_eq he hc) t

/-- No minting for `Step'`. -/
theorem noMinting_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (hc : CryptoHyp P txs) (t : P.Token) : liveValue st t ≤ st.deposited t := by
  obtain ⟨txs₀, h₀, he⟩ := h.to_run
  exact noMinting_proof P sup txs₀ st h₀ (cryptoHyp_of_eraseSnap_eq he hc) t

/-- Balance equals live value for `Step'`. -/
theorem balanceIsLiveValue_prov (sup : P.Token → Prop) (txs : List (Tx P)) (st : St P)
    (h : Run' sup txs st) (hc : CryptoHyp P txs) (t : P.Token) : st.balance t = liveValue st t := by
  obtain ⟨txs₀, h₀, he⟩ := h.to_run
  exact balanceIsLiveValue_proof P sup txs₀ st h₀ (cryptoHyp_of_eraseSnap_eq he hc) t

end LeanShieldedPool.Refine
