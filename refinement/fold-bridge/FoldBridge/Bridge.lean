import Merkle.Fold
import Tree.LeanImt

/-!
# The field-to-Nat bridge between the circuit's fold and the LeanIMT tree fold

The circuit fold of `circuits-lampe/` (`Merkle.Fold.merkleRoot`) folds over `Fp p` with a `U 32`
depth; it is the value of the extracted `binary_merkle_root<N>` (`Merkle.Fold.bmr_fwd`). The
LeanIMT module of this package (`LeanImt.merkleRoot`, `Tree/LeanImt.lean`) folds the same
loop over `Nat` with an abstract hash and proves completeness and binding against the LeanIMT
model. This file connects them, in the Lampe environment of `circuits-lampe/`:

* `Hn h a b = (h (a : Fp p) (b : Fp p)).val`: the field hash read on words.
* `merkleRoot_val`: the value of the circuit's field fold is the LeanIMT module's `Nat` fold under `Hn h`, of the
  values of the leaf and path, at depth `depth.toNat`. For every hash, width, depth, bits and path.
* `complete_field`, `binding_field`, `binding_mem_or_bad_field`: the LeanIMT completeness and binding
  restated for the field fold.
* `bad_field`: under the Solidity range check (every leaf below the field modulus), the
  `LeanImt.Bad` event for a field path is a field-level bad event: a real `h` collision of field elements, a
  leaf that is an `h` output of tree children, or an `h` output that is a leaf (or 0).
* `FoldBridge/Compose.lean`: W2 and T3 composed with the binding.
-/

namespace FoldBridge
open Lampe LeanShieldedPool.Refine LeanShieldedPool.Refine.LeanImt

section
variable {p : Prime}

/-- The field hash read on words: the inputs are cast into the field, the output is its value. -/
def Hn (h : Fp p → Fp p → Fp p) (a b : ℕ) : ℕ := (h (a : Fp p) (b : Fp p)).val

theorem cast_val (x : Fp p) : ((x.val : ℕ) : Fp p) = x := ZMod.natCast_zmod_val x

theorem Hn_lt (h : Fp p → Fp p → Fp p) (a b : ℕ) : Hn h a b < p.natVal := ZMod.val_lt _

theorem getD_cast (P : List ℕ) (i : ℕ) :
    (P.map (fun x : ℕ => (x : Fp p))).getD i 0 = ((P.getD i 0 : ℕ) : Fp p) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[i]? <;> simp

/-- One loop step: the LeanIMT step on the value of a field node is the value of the circuit's step, for a
`Nat` path cast into the field. -/
theorem level_cast (h : Fp p → Fp p → Fp p) (depth : ℕ) (I : List Bool) (P : List ℕ)
    (xF : Fp p) (i : ℕ) :
    LeanImt.level (Hn h) depth I P xF.val i =
      (Merkle.Fold.level h depth I (P.map (fun x : ℕ => (x : Fp p))) xF i).val := by
  unfold LeanImt.level Merkle.Fold.level
  split_ifs <;> simp only [Hn, getD_cast, cast_val]

theorem fold_cast (h : Fp p → Fp p → Fp p) (depth : ℕ) (I : List Bool) (P : List ℕ) :
    ∀ (l : List ℕ) (xF : Fp p),
      l.foldl (LeanImt.level (Hn h) depth I P) xF.val =
        (l.foldl (Merkle.Fold.level h depth I (P.map (fun x : ℕ => (x : Fp p)))) xF).val
  | [], _ => rfl
  | i :: l, xF => by
    simp only [List.foldl_cons]
    rw [level_cast]
    exact fold_cast h depth I P l _

/-- **The bridge, cast form.** A `Nat` path cast into the field: the value of the circuit's field fold is
the LeanIMT fold under `Hn h`. -/
theorem merkleRoot_cast (h : Fp p → Fp p → Fp p) {n : ℕ} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool n) (P : List.Vector ℕ n) :
    (Merkle.Fold.merkleRoot h leaf depth indices (P.map (fun x : ℕ => (x : Fp p)))).val =
      LeanImt.merkleRoot (Hn h) leaf.val depth.toNat indices P := by
  unfold Merkle.Fold.merkleRoot LeanImt.merkleRoot
  rw [List.Vector.toList_map, fold_cast]

theorem map_val_cast {n : ℕ} (path : List.Vector (Fp p) n) :
    (path.map (·.val)).map (fun x : ℕ => (x : Fp p)) = path := by
  apply List.Vector.toList_injective
  simp only [List.Vector.toList_map, List.map_map]
  conv_rhs => rw [← List.map_id path.toList]
  exact List.map_congr_left (fun x _ => cast_val x)

/-- **The bridge.** For every hash `h`, width `n`, leaf, depth, direction bits and path of field
elements: the value of the circuit's field fold is the LeanIMT module's `Nat` fold under `Hn h` of the values. -/
theorem merkleRoot_val (h : Fp p → Fp p → Fp p) {n : ℕ} (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool n) (path : List.Vector (Fp p) n) :
    (Merkle.Fold.merkleRoot h leaf depth indices path).val =
      LeanImt.merkleRoot (Hn h) leaf.val depth.toNat indices (path.map (·.val)) := by
  rw [← merkleRoot_cast, map_val_cast]

/-! ## The LeanIMT completeness and binding for the field fold -/

/-- **Completeness, field fold (width 32).** Every leaf of the contract tree of at most `2 ^ 32`
words that is a field element has a circuit witness: a `U 32` `proof_length ≤ 32`, direction bits
and a path of field elements, whose field fold has the contract root as its value. -/
theorem complete_field (h : Fp p → Fp p → Fp p) (L : List ℕ) (hN : L.length ≤ 2 ^ 32)
    (leaf : Fp p) (hm : leaf.val ∈ L) :
    ∃ (len : U 32) (I : List.Vector Bool 32) (P : List.Vector (Fp p) 32),
      len.toNat ≤ 32 ∧ (Merkle.Fold.merkleRoot h leaf len I P).val = rootOf (Hn h) L := by
  obtain ⟨len, I, P, hlen, hroot⟩ := complete_mem (Hn h) L hN leaf.val hm
  have hl : (BitVec.ofNat 32 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨BitVec.ofNat 32 len, I, P.map (fun x : ℕ => (x : Fp p)), by omega, ?_⟩
  rw [merkleRoot_cast, hl, hroot]

/-- Completeness for a word leaf below the field modulus (the Solidity `_insert` range check). -/
theorem complete_word (h : Fp p → Fp p → Fp p) (L : List ℕ) (hN : L.length ≤ 2 ^ 32)
    (x : ℕ) (hm : x ∈ L) (hx : x < p.natVal) :
    ∃ (len : U 32) (I : List.Vector Bool 32) (P : List.Vector (Fp p) 32),
      len.toNat ≤ 32 ∧ (Merkle.Fold.merkleRoot h (x : Fp p) len I P).val = rootOf (Hn h) L := by
  apply complete_field h L hN
  rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hx]

/-- **Binding, field fold.** If the value of the field fold is the contract root of `L`,
`LeanImt.Outcome` holds for the values of the leaf and of the active path. -/
theorem binding_field (h : Fp p → Fp p → Fp p) (L : List ℕ) (leaf : Fp p) (d : U 32) {n : ℕ}
    (I : List.Vector Bool n) (path : List.Vector (Fp p) n)
    (hr : (Merkle.Fold.merkleRoot h leaf d I path).val = rootOf (Hn h) L) :
    Outcome (Hn h) (imtOf (Hn h) L).depth L leaf.val
      (activePath d.toNat I.toList (path.map (·.val)).toList n) :=
  binding (Hn h) L leaf.val d.toNat I (path.map (·.val)) (by rw [← merkleRoot_val]; exact hr)

/-- **Binding, per-path form, field fold.** For a nonzero field leaf: its value is a leaf of `L`,
or `LeanImt.Bad` holds for this path. -/
theorem binding_mem_or_bad_field (h : Fp p → Fp p → Fp p) (L : List ℕ) (leaf : Fp p) (d : U 32)
    {n : ℕ} (I : List.Vector Bool n) (path : List.Vector (Fp p) n) (hne : leaf ≠ 0)
    (hr : (Merkle.Fold.merkleRoot h leaf d I path).val = rootOf (Hn h) L) :
    leaf.val ∈ L ∨
      Bad (Hn h) (imtOf (Hn h) L).depth L leaf.val
        (activePath d.toNat I.toList (path.map (·.val)).toList n) :=
  binding_mem_or_bad (Hn h) L leaf.val d.toNat I (path.map (·.val))
    (fun h0 => hne ((ZMod.val_eq_zero leaf).1 h0)) (by rw [← merkleRoot_val]; exact hr)

/-- The circuit equation form (W2, T3): `root = merkleRoot h leaf d I path` for a public field
`root` whose value is the contract root. -/
theorem binding_eq (h : Fp p → Fp p → Fp p) (L : List ℕ) (root leaf : Fp p) (d : U 32) {n : ℕ}
    (I : List.Vector Bool n) (path : List.Vector (Fp p) n) (hne : leaf ≠ 0)
    (heq : root = Merkle.Fold.merkleRoot h leaf d I path) (hroot : root.val = rootOf (Hn h) L) :
    leaf.val ∈ L ∨
      Bad (Hn h) (imtOf (Hn h) L).depth L leaf.val
        (activePath d.toNat I.toList (path.map (·.val)).toList n) :=
  binding_mem_or_bad_field h L leaf d I path hne (heq ▸ hroot)

/-- The circuit relation `InclC` holds for the value of every accepted width-32 field fold. -/
theorem inclC_of_field (h : Fp p → Fp p → Fp p) (leaf : Fp p) (d : U 32)
    (I : List.Vector Bool 32) (path : List.Vector (Fp p) 32) (hd : d.toNat ≤ 32) :
    InclC (Hn h) leaf.val (Merkle.Fold.merkleRoot h leaf d I path).val := by
  refine ⟨d.toNat, I, path.map (·.val), hd, ?_⟩
  exact (merkleRoot_val h leaf d I path).symm

/-! ## The bad event is a field-level bad event -/

/-- `LeanImt.Bad` read in the field: for the fold pairs of this path and the node pairs of the tree
of `L`, an `h` collision of two DISTINCT pairs of field elements (not only distinct words), or
the leaf is `h` of tree children, or `h` of a fold pair is a leaf of `L` (or 0 for the empty tree).
The pairs stay named: each case points at this path and this tree. -/
def BadF (h : Fp p → Fp p → Fp p) (l : ℕ) (L : List ℕ) (leaf : Fp p) (q : List (Bool × ℕ)) :
    Prop :=
  (∃ x y u v, (x, y) ∈ foldPairs (Hn h) leaf.val q ∧ (u, v) ∈ pairs (Hn h) l L ∧
      ((x : Fp p), (y : Fp p)) ≠ ((u : Fp p), (v : Fp p)) ∧
      h (x : Fp p) (y : Fp p) = h (u : Fp p) (v : Fp p)) ∨
    (∃ u v, (u, v) ∈ pairs (Hn h) l L ∧ leaf = h (u : Fp p) (v : Fp p)) ∨
    (∃ x y, (x, y) ∈ foldPairs (Hn h) leaf.val q ∧ Atom L (h (x : Fp p) (y : Fp p)).val)

theorem sub_lt (h : Fp p → Fp p → Fp p) :
    ∀ (l : ℕ) (M : List ℕ), (∀ x ∈ M, x < p.natVal) → sub (Hn h) l M < p.natVal
  | 0, M, hM => by
    cases M with
    | nil => exact Nat.pos_of_ne_zero (NeZero.ne _)
    | cons a M => exact hM a (by simp)
  | l + 1, M, hM => by
    simp only [sub]
    split_ifs
    · exact sub_lt h l M hM
    · exact Hn_lt h _ _

theorem pairs_lt (h : Fp p → Fp p → Fp p) :
    ∀ (l : ℕ) (M : List ℕ), (∀ x ∈ M, x < p.natVal) →
      ∀ u v, (u, v) ∈ pairs (Hn h) l M → u < p.natVal ∧ v < p.natVal
  | 0, _, _, _, _, hm => by simp [pairs] at hm
  | l + 1, M, hM, u, v, hm => by
    have ht : ∀ x ∈ M.take (2 ^ l), x < p.natVal := fun x hx => hM x (List.mem_of_mem_take hx)
    have hd : ∀ x ∈ M.drop (2 ^ l), x < p.natVal := fun x hx => hM x (List.mem_of_mem_drop hx)
    simp only [pairs] at hm
    split_ifs at hm
    · exact pairs_lt h l M hM u v hm
    · rcases List.mem_cons.1 hm with he | hm
      · cases he; exact ⟨sub_lt h l _ ht, sub_lt h l _ hd⟩
      · rcases List.mem_append.1 hm with hm | hm
        · exact pairs_lt h l _ ht u v hm
        · exact pairs_lt h l _ hd u v hm

theorem foldPairs_lt (h : Fp p → Fp p → Fp p) :
    ∀ (q : List (Bool × ℕ)) (x : ℕ), x < p.natVal → (∀ bs ∈ q, bs.2 < p.natVal) →
      ∀ a b, (a, b) ∈ foldPairs (Hn h) x q → a < p.natVal ∧ b < p.natVal
  | [], _, _, _, _, _, hm => by simp [foldPairs] at hm
  | bs :: q, x, hx, hq, a, b, hm => by
    simp only [foldPairs, List.mem_cons] at hm
    rcases hm with he | hm
    · have h2 := hq bs (by simp)
      unfold stepPair at he
      split_ifs at he <;> cases he <;> exact ⟨by assumption, by assumption⟩
    · exact foldPairs_lt h q _ (Hn_lt h _ _) (fun bs' hb => hq bs' (by simp [hb])) a b hm

theorem activePath_lt {n : ℕ} (d : ℕ) (I : List Bool) (path : List.Vector (Fp p) n) :
    ∀ bs ∈ activePath d I (path.map (·.val)).toList n, bs.2 < p.natVal := by
  intro bs hbs
  simp only [activePath, List.mem_map] at hbs
  obtain ⟨i, -, rfl⟩ := hbs
  simp only [List.Vector.toList_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (path.toList)[i]? with
  | none => exact Nat.pos_of_ne_zero (NeZero.ne _)
  | some y => exact ZMod.val_lt y

theorem val_inj_pair {a b c e : ℕ} (ha : a < p.natVal) (hb : b < p.natVal) (hc : c < p.natVal)
    (he : e < p.natVal) (hne : (a, b) ≠ (c, e)) :
    ((a : Fp p), (b : Fp p)) ≠ ((c : Fp p), (e : Fp p)) := by
  intro heq
  apply hne
  simp only [Prod.mk.injEq] at heq ⊢
  obtain ⟨h1, h2⟩ := heq
  have k1 := congrArg ZMod.val h1
  have k2 := congrArg ZMod.val h2
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt he] at k1 k2
  exact ⟨k1, k2⟩

/-- **`LeanImt.Bad` for a field path is a field-level bad event**, when every leaf of `L` is below
the field modulus (the Solidity `_insert` range check). So the `Nat` collision of `LeanImt.Bad` case is never a
mere wrap-around of a word modulo `p`: it names two distinct pairs of field elements. -/
theorem bad_field (h : Fp p → Fp p → Fp p) (L : List ℕ) (hL : ∀ x ∈ L, x < p.natVal)
    (leaf : Fp p) (d : ℕ) {n : ℕ} (I : List Bool) (path : List.Vector (Fp p) n)
    (hb : Bad (Hn h) (imtOf (Hn h) L).depth L leaf.val
      (activePath d I (path.map (·.val)).toList n)) :
    BadF h (imtOf (Hn h) L).depth L leaf (activePath d I (path.map (·.val)).toList n) := by
  rcases hb with ⟨x, y, u, v, hxy, huv, hne, heq⟩ | ⟨u, v, huv, hl⟩ | ⟨x, y, hxy, ha⟩
  · obtain ⟨hx, hy⟩ := foldPairs_lt h _ _ (ZMod.val_lt leaf) (activePath_lt d I path) x y hxy
    obtain ⟨hu, hv⟩ := pairs_lt h _ L hL u v huv
    exact Or.inl ⟨x, y, u, v, hxy, huv, val_inj_pair hx hy hu hv hne, ZMod.val_injective _ heq⟩
  · exact Or.inr (Or.inl ⟨u, v, huv, ZMod.val_injective _ hl⟩)
  · exact Or.inr (Or.inr ⟨x, y, hxy, ha⟩)

/-- Binding with the field-level bad event, in the circuit equation form. -/
theorem binding_mem_or_badF (h : Fp p → Fp p → Fp p) (L : List ℕ) (hL : ∀ x ∈ L, x < p.natVal)
    (root leaf : Fp p) (d : U 32) {n : ℕ} (I : List.Vector Bool n) (path : List.Vector (Fp p) n)
    (hne : leaf ≠ 0) (heq : root = Merkle.Fold.merkleRoot h leaf d I path)
    (hroot : root.val = rootOf (Hn h) L) :
    leaf.val ∈ L ∨
      BadF h (imtOf (Hn h) L).depth L leaf (activePath d.toNat I.toList (path.map (·.val)).toList n) :=
  (binding_eq h L root leaf d I path hne heq hroot).imp id (bad_field h L hL leaf _ _ path)

end

end FoldBridge
