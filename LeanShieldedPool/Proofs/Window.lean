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

theorem windowHead_proof (P : PrimSpec) : windowHead P :=
  fun _ _ _ hr => hr.window_head

/-- Leaves inserted by each operation (Section 4): one per deposit, two
per transfer, none per withdrawal. -/
def Tx.leafDelta : Tx P → Nat
  | .deposit _ => 1
  | .transfer _ => 2
  | .withdraw _ => 0

theorem Step.leaves_length {st st' : St P} {tx : Tx P} (h : Step st tx st') :
    st'.leaves.length = st.leaves.length + tx.leafDelta := by
  cases h with
  | @deposit d hg =>
      show ((st.minted ++ [d.note]).map Note.cm).length = (st.minted.map Note.cm).length + 1
      rw [List.length_map, List.length_append, List.length_map]
      rfl
  | @transfer d hg =>
      show ((st.minted ++ [d.out1, d.out2]).map Note.cm).length =
        (st.minted.map Note.cm).length + 2
      rw [List.length_map, List.length_append, List.length_map]
      rfl
  | withdraw hg => rfl

/-- The leaf count after a history is the sum of its insertions. -/
theorem Run.leaves_length {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (h : Run sup txs st) : st.leaves.length = (txs.map Tx.leafDelta).sum := by
  induction h with
  | empty => rfl
  | @step txs st st' tx hr hs ih =>
      rw [hs.leaves_length, ih, List.map_append, List.sum_append]
      rfl

private theorem sum_le_of_prefix {l₁ l₂ : List (Tx P)} (h : l₁ <+: l₂) :
    (l₁.map Tx.leafDelta).sum ≤ (l₂.map Tx.leafDelta).sum := by
  obtain ⟨tail, rfl⟩ := h
  rw [List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem noMidTransferRoot_proof (P : PrimSpec) : noMidTransferRoot P := by
  intro sup txs st hr stem d st₀ hp h0 hmem
  have hstem : stem <+: txs := (List.prefix_append stem _).trans hp
  have e0 := h0.leaves_length
  rcases windowBoundary_proof P sup txs st hr _ hmem with hz | ⟨lead, tx, st₁, st₂, hlead, h1, hs, hlen⟩
  · omega
  · have e2 := (Run.step h1 hs).leaves_length
    rcases Nat.lt_or_ge stem.length (lead ++ [tx]).length with hl | hl
    · have hle : (stem ++ [Tx.transfer d]).length ≤ (lead ++ [tx]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have hpq := sum_le_of_prefix (List.prefix_of_prefix_length_le hp hlead hle)
      rw [List.map_append, List.sum_append] at hpq
      have h2 : ([Tx.transfer d].map (Tx.leafDelta (P := P))).sum = 2 := rfl
      omega
    · have hqp := sum_le_of_prefix (List.prefix_of_prefix_length_le hlead hstem hl)
      omega

theorem honestWithdrawWindow_proof (P : PrimSpec) : honestWithdrawWindow P := by
  intro sup txs st hr k n r s hs hn hown hfresh hne hbal
  have htree : st.inTreeAt s n.cm := by
    show n.cm ∈ (st.minted.map Note.cm).take s
    rw [← List.map_take]
    exact List.mem_map_of_mem hn
  have hwf : U128 n.amount :=
    hr.runNotes_wf n (hr.minted_mem_runNotes (List.mem_of_mem_take hn))
  have hg : WithdrawData.guard ⟨k, n, r, s⟩ st :=
    ⟨hs, htree, hown, hfresh, hne, hwf, hbal⟩
  refine ⟨_, Step.withdraw hg, Run.step hr (Step.withdraw hg), ?_⟩
  show drop st.balance n.token n.amount n.token + n.amount = st.balance n.token
  rw [show drop st.balance n.token n.amount n.token = st.balance n.token - n.amount
    from if_pos rfl]
  exact Nat.sub_add_cancel hbal

theorem honestWithdraw_proof (P : PrimSpec) : honestWithdraw P := by
  intro sup txs st hr k n r hn hown hfresh hne hbal
  have hwin : st.leaves.length ∈ st.window := List.mem_of_mem_head? hr.window_head
  have hmem : n ∈ st.minted.take st.leaves.length := by
    show n ∈ st.minted.take (st.minted.map Note.cm).length
    rw [List.length_map, List.take_length]
    exact hn
  exact honestWithdrawWindow_proof P sup txs st hr k n r _ hwin hmem hown hfresh hne hbal

end LeanShieldedPool
