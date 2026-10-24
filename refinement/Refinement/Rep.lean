import Refinement.Storage

/-!
# The representation relation

`Rep H E sup L σ st` relates pool storage `σ` to a model state `st`. `L` is the ghost leaf
order (for an accepted history `h` it is `ghostLeaves h`), `sup` the model's supported set,
`H` the PoseidonT3 function of the tree, `E` the word encodings of the model carriers.

Roots enter by inclusion: every root `isKnownRoot` accepts is `rootOf H (L.take n)` for some
`n ∈ st.window` (`Rep.known_root_in_window`). The ring fields make that inclusion inductive.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-- Word encodings of the model's opaque carriers: a commitment or nullifier as its canonical
field element, a token or other address as its address word. -/
structure Enc (P : PrimSpec) where
  cm : P.Commitment → Nat
  nf : P.Nullifier → Nat
  tok : P.Token → Nat
  addr : P.Address → Nat

/-- The roots of the window's snapshots, newest first. -/
def windowRoots (H : Nat → Nat → Nat) (L : List Nat) (w : List Nat) : List Nat :=
  w.map (fun n => rootOf H (L.take n))

/-- The ring entry `j` records back from the newest: `historicalRoots[(index - 1 - j) mod 100]`. -/
def ringAt (σ : Storage) (j : Nat) : Nat := σ.ring ((σ.ringIndex + 99 - j) % 100)

/-- `Rep` without the valid-roots field. `Rep` adds that field; `RepCore` alone is the mutated
relation of the negative control (`Refinement/NonVacuity.lean`). -/
structure RepCore (H : Nat → Nat → Nat) (E : Enc P) (sup : P.Token → Prop) (L : List Nat)
    (σ : Storage) (st : St P) : Prop where
  /-- The model's leaves are the ghost leaves. -/
  leaves : st.leaves.map E.cm = L
  /-- The tree slots hold the LeanIMT of `L`; with it `size = L.length` and
  `commitmentRoot() = rootOf H L`. -/
  tree : σ.imt = imtOf H L
  /-- The `leaves` mapping marks exactly the ghost leaves. -/
  leafIndex : ∀ w, σ.leafIndex w ≠ 0 ↔ w ∈ L
  /-- The `nullifiers` mapping is the model's nullifier set. -/
  nullifiers : ∀ w, σ.nullifiers w = true ↔ w ∈ st.nullifiers.map E.nf
  /-- `supportedTokens ⊆ sup`. -/
  supported : ∀ t, σ.supportedTokens (E.tok t) = true → sup t
  /-- The model's supported set is `sup` (frozen, CLAUSEMAP simplification 10). -/
  supported_eq : st.supported = sup
  /-- `historicalRootIndex < 100`. -/
  ringIndex_lt : σ.ringIndex < 100
  /-- The ring holds the window's roots, newest first, zero past the window's end. -/
  ring : ∀ j < 100, ringAt σ j = (windowRoots H L st.window).getD j 0
  /-- The newest window entry is the current leaf count. -/
  head : st.window.head? = some L.length
  /-- Window entries are leaf counts of the current tree. -/
  window_le : ∀ n ∈ st.window, n ≤ L.length

/-- **The representation relation.** -/
structure Rep (H : Nat → Nat → Nat) (E : Enc P) (sup : P.Token → Prop) (L : List Nat)
    (σ : Storage) (st : St P) : Prop extends RepCore H E sup L σ st where
  /-- Every valid root is nonzero and sits in the ring. With `ring` this gives the window
  inclusion `known_root_in_window`. -/
  valid : ∀ r, σ.validRoots r = true → r ≠ 0 ∧ ∃ p < 100, σ.ring p = r

/-- **Genesis instance**: constructor storage represents the empty pool. No premise. -/
theorem rep_genesis (H : Nat → Nat → Nat) (E : Enc P) (sup : P.Token → Prop) (v reg o : Nat) :
    Rep H E sup [] (Storage.genesis v reg o) (St.empty P sup) where
  leaves := rfl
  tree := rfl
  leafIndex := fun w => by
    show (0 : Nat) ≠ 0 ↔ w ∈ ([] : List Nat)
    exact ⟨fun h => absurd rfl h, fun h => nomatch h⟩
  nullifiers := fun w => by
    show false = true ↔ w ∈ ([] : List Nat)
    exact ⟨fun h => absurd h Bool.false_ne_true, fun h => nomatch h⟩
  supported := fun _ h => absurd h Bool.false_ne_true
  supported_eq := rfl
  ringIndex_lt := by show (0 : Nat) < 100; omega
  ring := fun j _ => by
    show (0 : Nat) = [rootOf H (List.take 0 [])].getD j 0
    rcases j with _ | _ <;> rfl
  head := rfl
  window_le := fun n hn => by
    have h0 : n = 0 := List.mem_singleton.1 hn
    rw [h0]
    exact Nat.le_refl 0
  valid := fun _ h => absurd h Bool.false_ne_true

theorem getD_windowRoots_ne_zero {H : Nat → Nat → Nat} {L w : List Nat} {j r : Nat}
    (hj : (windowRoots H L w).getD j 0 = r) (hr : r ≠ 0) :
    ∃ n ∈ w, r = rootOf H (L.take n) := by
  unfold windowRoots at hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hj
  cases hw : w[j]? with
  | none =>
    rw [hw] at hj
    exact absurd hj.symm hr
  | some n =>
    rw [hw] at hj
    exact ⟨n, List.mem_of_getElem? hw, hj.symm⟩

/-- **Window inclusion**: every root the contract's `isKnownRoot` accepts is the root of a
leaf prefix whose length is in the model window. This is what `rootInWindow` needs. -/
theorem Rep.known_root_in_window {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ : Storage} {st : St P} (hR : Rep H E sup L σ st) {r : Nat}
    (hk : σ.isKnownRoot r) : ∃ n ∈ st.window, r = rootOf H (L.take n) := by
  rcases hk with hc | hv
  · refine ⟨L.length, List.mem_of_mem_head? hR.head, ?_⟩
    rw [hc, List.take_of_length_le (Nat.le_refl _)]
    exact congrArg Imt.root hR.tree
  · obtain ⟨hr0, p, hp, hpr⟩ := hR.valid r hv
    have hi := hR.ringIndex_lt
    have hj : (σ.ringIndex + 99 - (σ.ringIndex + 99 - p) % 100) % 100 = p := by omega
    have h1 := hR.ring ((σ.ringIndex + 99 - p) % 100) (Nat.mod_lt _ (by omega))
    unfold ringAt at h1
    rw [hj, hpr] at h1
    exact getD_windowRoots_ne_zero h1.symm hr0

/-- `Rep` is stable under storage changes that touch only `supportedTokens`, `verifier`,
`attestationRegistry` or `owner`, as long as the new supported set stays inside `sup`. -/
theorem Rep.frame {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ σ' : Storage} {st : St P} (hR : Rep H E sup L σ st)
    (himt : σ'.imt = σ.imt) (hli : σ'.leafIndex = σ.leafIndex) (hring : σ'.ring = σ.ring)
    (hri : σ'.ringIndex = σ.ringIndex) (hv : σ'.validRoots = σ.validRoots)
    (hn : σ'.nullifiers = σ.nullifiers)
    (hs : ∀ t, σ'.supportedTokens (E.tok t) = true → sup t) : Rep H E sup L σ' st where
  leaves := hR.leaves
  tree := himt.trans hR.tree
  leafIndex := fun w => by rw [hli]; exact hR.leafIndex w
  nullifiers := fun w => by rw [hn]; exact hR.nullifiers w
  supported := hs
  supported_eq := hR.supported_eq
  ringIndex_lt := by rw [hri]; exact hR.ringIndex_lt
  ring := fun j hj => by
    unfold ringAt
    rw [hring, hri]
    exact hR.ring j hj
  head := hR.head
  window_le := hR.window_le
  valid := fun r h => by
    rw [hv] at h
    obtain ⟨a, p, hp, e⟩ := hR.valid r h
    exact ⟨a, p, hp, by rw [hring]; exact e⟩

end LeanShieldedPool.Refine
