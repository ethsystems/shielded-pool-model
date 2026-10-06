import LeanShieldedPool.Statements.Window
import LeanShieldedPool.Proofs.Invariants

namespace LeanShieldedPool

variable {P : PrimSpec}

theorem St.mem_pushWindow {w : List Nat} {n s : Nat}
    (h : s ∈ St.pushWindow w n) : s = n ∨ s ∈ w :=
  List.mem_cons.mp (List.mem_of_mem_take h)

/-- A step either keeps the window and the tree, or pushes the leaf count of
its post-state. -/
theorem Step.window_eq {st st' : St P} {tx : Tx P} (h : Step st tx st') :
    (st'.window = st.window ∧ st'.leaves = st.leaves) ∨
      st'.window = St.pushWindow st.window st'.leaves.length := by
  cases h with
  | @deposit d hg =>
      right
      show St.pushWindow st.window (st.minted.length + 1) =
        St.pushWindow st.window ((st.minted ++ [d.note]).map Note.cm).length
      rw [List.length_map, List.length_append]
      rfl
  | @transfer d hg =>
      right
      show St.pushWindow st.window (st.minted.length + 2) =
        St.pushWindow st.window ((st.minted ++ [d.out1, d.out2]).map Note.cm).length
      rw [List.length_map, List.length_append]
      rfl
  | withdraw hg =>
      left
      exact ⟨rfl, rfl⟩

/-- The newest window entry is the current root. -/
theorem Run.window_head {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) :
    st.window.head? = some st.leaves.length := by
  induction h with
  | empty => rfl
  | @step txs st st' tx hr hs ih =>
      rcases hs.window_eq with ⟨hw, hl⟩ | hw
      · rw [hw, hl]
        exact ih
      · rw [hw]
        rfl

private theorem boundary_extend {sup : P.Token → Prop}
    {txs : List (Tx P)} {tx : Tx P} {s : Nat}
    (h : s = 0 ∨ ∃ (pre : List (Tx P)) (tx' : Tx P) (st₀ st₁ : St P),
      pre ++ [tx'] <+: txs ∧ Run sup pre st₀ ∧ Step st₀ tx' st₁ ∧
      s = st₁.leaves.length) :
    s = 0 ∨ ∃ (pre : List (Tx P)) (tx' : Tx P) (st₀ st₁ : St P),
      pre ++ [tx'] <+: txs ++ [tx] ∧ Run sup pre st₀ ∧ Step st₀ tx' st₁ ∧
      s = st₁.leaves.length := by
  rcases h with h | ⟨pre, tx', st₀, st₁, hp, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨pre, tx', st₀, st₁, hp.trans (List.prefix_append _ _), h1, h2, h3⟩

theorem windowBoundary_proof (P : PrimSpec) : windowBoundary P := by
  intro sup txs st hr
  induction hr with
  | empty =>
      intro s hs
      exact Or.inl (List.mem_singleton.mp hs)
  | @step txs st st' tx hr hs ih =>
      intro s hsw
      rcases hs.window_eq with ⟨hw, _⟩ | hw
      · rw [hw] at hsw
        exact boundary_extend (ih s hsw)
      · rw [hw] at hsw
        rcases St.mem_pushWindow hsw with h | h
        · exact Or.inr ⟨txs, tx, st, st', List.prefix_refl _, hr, hs, h⟩
        · exact boundary_extend (ih s h)

theorem honestWithdraw_proof (P : PrimSpec) : honestWithdraw P := by
  intro sup txs st hr k n r hn hown hfresh hne hbal
  have hwin : st.rootInWindow st.leaves.length :=
    List.mem_of_mem_head? hr.window_head
  have htree : st.inTreeAt st.leaves.length n.cm := by
    unfold St.inTreeAt
    rw [List.take_length]
    exact List.mem_map_of_mem hn
  have hwf : U128 n.amount := hr.runNotes_wf n (hr.minted_mem_runNotes hn)
  have hg : WithdrawData.guard ⟨k, n, r, st.leaves.length⟩ st :=
    ⟨hwin, htree, hown, hfresh, hne, hwf, hbal⟩
  refine ⟨_, Step.withdraw hg, Run.step hr (Step.withdraw hg), ?_⟩
  show drop st.balance n.token n.amount n.token + n.amount = st.balance n.token
  rw [show drop st.balance n.token n.amount n.token = st.balance n.token - n.amount
    from if_pos rfl]
  exact Nat.sub_add_cancel hbal

end LeanShieldedPool
