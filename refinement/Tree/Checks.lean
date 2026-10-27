import Tree.LeanImt
import Mathlib.Data.Nat.Pairing

/-!
# LeanIMT checks: non-vacuity on a 3-leaf tree, structural cases, and fold-direction controls
-/

namespace LeanShieldedPool.Refine.LeanImt.Checks

open LeanShieldedPool.Refine LeanShieldedPool.Refine.LeanImt

/-! ## Non-vacuity, abstract hash -/

section
variable (H : Nat → Nat → Nat) (a b c : Nat)

/-- Three leaves: depth 2; the third leaf has no right sibling at level 0 and is carried up. -/
theorem three_depth : (imtOf H [a, b, c]).depth = 2 := rfl

theorem three_sub : sub H 2 [a, b, c] = H (H a b) c := rfl

theorem three_root : rootOf H [a, b, c] = H (H a b) c := by
  rw [rootOf_eq_sub, three_depth, three_sub]

/-- The compressed proofs: two levels for `a` and `b`, one level for `c` (level 0 skipped). -/
theorem three_proofs :
    proof H 2 [a, b, c] 0 = [(false, b), (false, c)] ∧
    proof H 2 [a, b, c] 1 = [(true, a), (false, c)] ∧
    proof H 2 [a, b, c] 2 = [(true, H a b)] := ⟨rfl, rfl, rfl⟩

/-- The circuit fold (width 32) on the three compressed proofs returns the contract root. -/
theorem three_circuit :
    merkleRoot H a 2 (padI [(false, b), (false, c)] 32 (by simp))
        (padP [(false, b), (false, c)] 32 (by simp)) = rootOf H [a, b, c] ∧
    merkleRoot H b 2 (padI [(true, a), (false, c)] 32 (by simp))
        (padP [(true, a), (false, c)] 32 (by simp)) = rootOf H [a, b, c] ∧
    merkleRoot H c 1 (padI [(true, H a b)] 32 (by simp))
        (padP [(true, H a b)] 32 (by simp)) = rootOf H [a, b, c] := by
  refine ⟨(merkleRoot_pad H a [(false, b), (false, c)] 32 (by simp)).trans ?_,
    (merkleRoot_pad H b [(true, a), (false, c)] 32 (by simp)).trans ?_,
    (merkleRoot_pad H c [(true, H a b)] 32 (by simp)).trans ?_⟩ <;> rw [three_root] <;> rfl

/-- The side-node slots after three inserts, as a hand run of `_insert` gives them: level 0 holds
`c` (written at index 2), level 1 holds `H a b`, level 2 (the root) holds `H (H a b) c`. -/
theorem three_trace :
    (imtOf H [a, b, c]).size = 3 ∧ (imtOf H [a, b, c]).side 0 = c ∧
    (imtOf H [a, b, c]).side 1 = H a b ∧ (imtOf H [a, b, c]).side 2 = H (H a b) c := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [imtOf, Imt.empty, List.foldl_cons, imtInsert, zero_add, pow_zero, lt_self_iff_false,
      ↓reduceIte, List.range_zero, List.foldl_nil, Nat.reduceAdd, Order.lt_two_iff, Std.le_refl,
      List.range_succ, List.nil_append, imtStep, Nat.shiftRight_zero, Nat.mod_succ, Function.update,
      ↓reduceDIte, pow_one, Nat.lt_add_one, List.cons_append, Nat.mod_self, zero_ne_one,
      Nat.reduceShiftRight, one_ne_zero, OfNat.zero_ne_ofNat]
  · simp only [imtOf, Imt.empty, List.foldl_cons, imtInsert, zero_add, pow_zero, lt_self_iff_false,
      ↓reduceIte, List.range_zero, List.foldl_nil, Nat.reduceAdd, Order.lt_two_iff, Std.le_refl,
      List.range_succ, List.nil_append, imtStep, Nat.shiftRight_zero, Nat.mod_succ, Function.update,
      ↓reduceDIte, pow_one, Nat.lt_add_one, List.cons_append, Nat.mod_self, zero_ne_one,
      Nat.reduceShiftRight, one_ne_zero, OfNat.one_ne_ofNat]
  · have := three_root H a b c
    rw [rootOf, Imt.root, three_depth] at this
    exact this

/-- `complete` applies to every leaf of the 3-leaf tree. -/
theorem three_complete : ∀ leaf ∈ [a, b, c], InclC H leaf (rootOf H [a, b, c]) :=
  fun leaf hm => inclC_of_mem H [a, b, c] (by simp) leaf hm

end

/-! ## A concrete injective hash: `Nat.pair x y + 1` -/

/-- Injective and never 0. -/
def Hp (x y : Nat) : Nat := Nat.pair x y + 1

theorem Hp_root : rootOf Hp [1, 2, 3] = 46 := by decide

/-- Structural case 1 occurs: the internal node value `Hp 1 2 = 6` is not a leaf, yet a one-level
path folds it to the root. `binding` classifies it as `nodeAsLeaf`, not `member`. -/
theorem nodeAsLeaf_occurs :
    InclC Hp 6 (rootOf Hp [1, 2, 3]) ∧ 6 ∉ [1, 2, 3] ∧
      Bad Hp (imtOf Hp [1, 2, 3]).depth [1, 2, 3] 6
        (activePath 1 (padI [(false, 3)] 32 (by decide)).toList
          (padP [(false, 3)] 32 (by decide)).toList 32) := by
  have hr : merkleRoot Hp 6 1 (padI [(false, 3)] 32 (by decide)) (padP [(false, 3)] 32 (by decide))
      = rootOf Hp [1, 2, 3] := by decide
  refine ⟨⟨1, _, _, by decide, hr⟩, by decide, ?_⟩
  rcases (binding Hp [1, 2, 3] 6 1 _ _ hr).member_or_bad with hm | hb
  · exfalso; rcases hm with hm | ⟨hm, _⟩
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
  · exact hb

/-- A colliding hash: `x + y + 1`. -/
def Hadd (x y : Nat) : Nat := x + y + 1

/-- The collision case occurs: under `Hadd`, the non-leaf 3 folds to the root of `[1, 2]` with
the sibling 0, and `binding` returns `Bad`; the only disjunct that can hold is the collision
`Hadd 3 0 = Hadd 1 2`. -/
theorem collision_occurs :
    InclC Hadd 3 (rootOf Hadd [1, 2]) ∧ 3 ∉ [1, 2] ∧
      Bad Hadd (imtOf Hadd [1, 2]).depth [1, 2] 3
        (activePath 1 (padI [(false, 0)] 32 (by decide)).toList
          (padP [(false, 0)] 32 (by decide)).toList 32) := by
  have hr : merkleRoot Hadd 3 1 (padI [(false, 0)] 32 (by decide))
      (padP [(false, 0)] 32 (by decide)) = rootOf Hadd [1, 2] := by decide
  refine ⟨⟨1, _, _, by decide, hr⟩, by decide, ?_⟩
  rcases binding_mem_or_bad Hadd [1, 2] 3 1 _ _ (by decide) hr with hm | hb
  · exact absurd hm (by decide)
  · exact hb

/-- Structural case 2 occurs: a stored leaf equals a hash output (`Hp 5 6 = 72`), so its
preimage input 5 folds to the root through it. -/
theorem leafAsNode_occurs :
    InclC Hp 5 (rootOf Hp [1, 2, Hp 5 6]) ∧ 5 ∉ [1, 2, Hp 5 6] := by
  refine ⟨⟨2, padI [(false, 6), (true, Hp 1 2)] 32 (by decide),
    padP [(false, 6), (true, Hp 1 2)] 32 (by decide), by decide, by decide⟩, by decide⟩

/-! ## Controls: the fold direction -/

/-- Mutant 1: the direction is flipped (bit `false` puts the node on the RIGHT). -/
def levelFlip (H : Nat → Nat → Nat) (depth : Nat) (indices : List Bool) (path : List Nat)
    (node i : Nat) : Nat :=
  if i < depth then
    if indices.getD i false then H node (path.getD i 0) else H (path.getD i 0) node
  else node

def merkleRootFlip (H : Nat → Nat → Nat) {n : Nat} (leaf depth : Nat)
    (indices : List.Vector Bool n) (path : List.Vector Nat n) : Nat :=
  (List.range n).foldl (levelFlip H depth indices.toList path.toList) leaf

/-- **Control 1 [checked].** With the flipped direction, the completeness statement with the
constructed compressed proof is false: leaf 2 (index 1) of `[1, 2, 3]` under `Hp`. -/
theorem control_flip_breaks_complete :
    ¬ ∀ (L : List Nat) (i leaf : Nat), L[i]? = some leaf → ∀ (hN : L.length ≤ 2 ^ 32),
      merkleRootFlip Hp leaf (proof Hp (imtOf Hp L).depth L i).length
        (padI (proof Hp (imtOf Hp L).depth L i) 32 (by
          have := proof_length Hp (imtOf Hp L).depth L i
          have := depth_le Hp L 32 hN; omega))
        (padP (proof Hp (imtOf Hp L).depth L i) 32 (by
          have := proof_length Hp (imtOf Hp L).depth L i
          have := depth_le Hp L 32 hN; omega)) = rootOf Hp L := by
  intro h
  have := h [1, 2, 3] 1 2 rfl (by decide)
  revert this
  decide

/-- Mutant 2: the direction is ignored (the node is always on the left). -/
def levelLeft (H : Nat → Nat → Nat) (depth : Nat) (path : List Nat) (node i : Nat) : Nat :=
  if i < depth then H node (path.getD i 0) else node

def merkleRootLeft (H : Nat → Nat → Nat) {n : Nat} (leaf depth : Nat)
    (path : List.Vector Nat n) : Nat :=
  (List.range n).foldl (levelLeft H depth path.toList) leaf

/-- The values that reach 46 by left-only steps under `Hp`. -/
def spine46 : List Nat := [46, 6, 1, 0]

theorem Hp_spine (x s : Nat) (h : Hp x s ∈ spine46) : x ∈ spine46 := by
  simp only [spine46, List.mem_cons, List.not_mem_nil, or_false, Hp] at h ⊢
  rcases h with h | h | h | h
  · have h' : Nat.pair x s = Nat.pair 6 3 := by rw [show Nat.pair 6 3 = 45 by decide]; omega
    exact Or.inr (Or.inl (Nat.pair_eq_pair.1 h').1)
  · have h' : Nat.pair x s = Nat.pair 1 2 := by rw [show Nat.pair 1 2 = 5 by decide]; omega
    exact Or.inr (Or.inr (Or.inl (Nat.pair_eq_pair.1 h').1))
  · have h' : Nat.pair x s = Nat.pair 0 0 := by rw [show Nat.pair 0 0 = 0 by decide]; omega
    exact Or.inr (Or.inr (Or.inr (Nat.pair_eq_pair.1 h').1))
  · omega

theorem left_spine (depth : Nat) (path : List Nat) (v : Nat) :
    ∀ m, (List.range m).foldl (levelLeft Hp depth path) v ∈ spine46 → v ∈ spine46 := by
  intro m
  induction m with
  | zero => exact id
  | succ m ih =>
    intro h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    unfold levelLeft at h
    split_ifs at h
    · exact ih (Hp_spine _ _ h)
    · exact ih h

/-- **Control 2 [checked].** With the direction ignored, completeness fails outright: no
`proof_length`, `indices` or `path` of any width folds leaf 3 of `[1, 2, 3]` to the root under
`Hp`. -/
theorem control_left_breaks_complete :
    ¬ ∃ (n d : Nat) (P : List.Vector Nat n), merkleRootLeft Hp 3 d P = rootOf Hp [1, 2, 3] := by
  rintro ⟨n, d, P, h⟩
  rw [Hp_root] at h
  have := left_spine d P.toList 3 n (by rw [merkleRootLeft] at h; rw [h]; decide)
  revert this; decide

/-- Why the flip is not an existential control: flipping every direction is the same as negating
every bit, so the existential form of completeness survives it. The bit convention is fixed by
`complete`'s construction, which `control_flip_breaks_complete` tests. -/
theorem flip_eq_negated_bits (H : Nat → Nat → Nat) {n : Nat} (leaf d : Nat)
    (I : List.Vector Bool n) (P : List.Vector Nat n) :
    merkleRootFlip H leaf d I P = merkleRoot H leaf d (I.map (fun b => !b)) P := by
  unfold merkleRootFlip merkleRoot
  suffices h : ∀ m, m ≤ n → (List.range m).foldl (levelFlip H d I.toList P.toList) leaf =
      (List.range m).foldl (level H d (I.map (fun b => !b)).toList P.toList) leaf from h n le_rfl
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, levelFlip, level, List.Vector.toList_map]
    have hlen : m < I.toList.length := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
    by_cases hd : m < d <;> cases hb : I.toList[m] <;> simp only [hd, ↓reduceIte,
        Bool.false_eq_true, Bool.not_false, Bool.not_true]

/-! ## Control: the contract's hash order -/

/-- Mutant 3: `_insert` with the hash inputs swapped (`H node sideNodes[level]`). -/
def imtStepSwap (H : Nat → Nat → Nat) (index : Nat) (acc : Nat × (Nat → Nat)) (level : Nat) :
    Nat × (Nat → Nat) :=
  if (index >>> level) % 2 = 1 then (H acc.1 (acc.2 level), acc.2)
  else (acc.1, Function.update acc.2 level acc.1)

def imtInsertSwap (H : Nat → Nat → Nat) (t : Imt) (leaf : Nat) : Imt :=
  let d := if 2 ^ t.depth < t.size + 1 then t.depth + 1 else t.depth
  let r := (List.range d).foldl (imtStepSwap H t.size) (leaf, t.side)
  ⟨t.size + 1, d, Function.update r.2 d r.1⟩

/-- **Control 3 [checked].** With the insert's hash order swapped, the tree root is no longer the
specification root, so `rootOf_eq_sub` depends on the order `H sideNodes[level] node`. -/
theorem control_swap_insert :
    ([1, 2, 3].foldl (imtInsertSwap Hp) Imt.empty).root ≠ sub Hp 2 [1, 2, 3] := by decide

/-- Mutant 4: a zero-padded tree (BinaryIMT style: a missing right child is 0 and is hashed). -/
def subZ (H : Nat → Nat → Nat) : Nat → List Nat → Nat
  | 0, M => M.headD 0
  | l + 1, M => H (subZ H l (M.take (2 ^ l))) (subZ H l (M.drop (2 ^ l)))

/-- **Control 4 [checked].** The contract tree is not the zero-padded tree: the carry-up rule
matters, and `sub` models it. -/
theorem control_zero_pad : rootOf Hp [1, 2, 3] ≠ subZ Hp 2 [1, 2, 3] := by decide

/-! ## Relation to the refinement's premises -/

/-- With `treeLink`, the refinement's `tree_member` needs only `TreeHyp (CollC H)`. -/
theorem member_of_treeHyp (H : Nat → Nat → Nat) {G W L : List Nat} {leaf : Nat}
    (hTH : TreeHyp (CollC H) G W) (hL : L <+: G) (hw : leaf ∈ W)
    (hi : InclC H leaf (rootOf H L)) : leaf ∈ L :=
  tree_member (treeLink H G W) hTH hL hw hi

/-- **Scope limit of `TreeHyp.no_bad` with `CollC` (checked).** If `H` is surjective in the second argument for every fixed
first argument, `CollC` holds for every nonzero non-member of every tree. So `¬ CollC` is a real
restriction on `H` and on the words, not a consequence of collision resistance alone: `CollC`
quantifies over all paths. Compression alone does not establish the surjectivity hypothesis. -/
theorem collC_of_onto (H : Nat → Nat → Nat) (hH : ∀ x r, ∃ s, H x s = r) (L : List Nat)
    (leaf : Nat) (hne : leaf ≠ 0) (hm : leaf ∉ L) : CollC H L leaf := by
  rcases (treeLink H L [leaf]).reduction L (List.prefix_refl L) leaf (List.mem_singleton_self _) hne
      (inclC_of_onto H hH leaf (rootOf H L)) with h | h
  · exact absurd h hm
  · exact h

end LeanShieldedPool.Refine.LeanImt.Checks
