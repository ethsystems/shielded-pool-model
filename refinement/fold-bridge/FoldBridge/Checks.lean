import FoldBridge.Bridge

/-!
# Fold bridge checks: the bridge on a concrete path, for an abstract hash (a reading check of the
conventions on both sides), and the depth-0 case.
-/

namespace FoldBridge.Checks
open Lampe LeanShieldedPool.Refine LeanShieldedPool.Refine.LeanImt FoldBridge

variable {p : Prime}

/-- Depth 2 of width 3, bits `[true, false, true]`: both folds give `h (h a leaf) b`; the third
position is inactive on both sides. -/
theorem bridge_example (h : Fp p → Fp p → Fp p) (leaf a b c : Fp p) :
    LeanImt.merkleRoot (Hn h) leaf.val (2 : U 32).toNat (⟨[true, false, true], rfl⟩ : List.Vector Bool 3)
        (List.Vector.map (·.val) (⟨[a, b, c], rfl⟩ : List.Vector (Fp p) 3)) = (h (h a leaf) b).val :=
  (merkleRoot_val h leaf (2 : U 32) ⟨[true, false, true], rfl⟩ ⟨[a, b, c], rfl⟩).symm.trans
    (congrArg ZMod.val (Merkle.Fold.merkleRoot_example h leaf a b c))

/-- The same value computed on the `Nat` side alone, from the definition of `Hn`. -/
theorem nat_side_example (h : Fp p → Fp p → Fp p) (leaf a b c : Fp p) :
    LeanImt.merkleRoot (Hn h) leaf.val 2 (⟨[true, false, true], rfl⟩ : List.Vector Bool 3)
        (⟨[a.val, b.val, c.val], rfl⟩ : List.Vector ℕ 3) =
      Hn h (Hn h a.val leaf.val) b.val := by
  rfl

/-- **Control (semantic): the bridge with the `Nat` hash inputs swapped is false.** With the
left projection `h a _ = a`, leaf 1, depth 1 and bit `false`, the circuit's field fold gives 1 while the
swapped `Nat` fold gives `(h 0 1).val = 0`. -/
theorem control_flip_false :
    ¬ ∀ (h : Fp p → Fp p → Fp p) (leaf : Fp p) (depth : U 32) (indices : List.Vector Bool 1)
        (path : List.Vector (Fp p) 1),
      (Merkle.Fold.merkleRoot h leaf depth indices path).val =
        LeanImt.merkleRoot (fun a b => Hn h b a) leaf.val depth.toNat indices (path.map (·.val)) := by
  intro H
  have k := H (fun a _ => a) 1 1 (false ::ᵥ List.Vector.nil) (0 ::ᵥ List.Vector.nil)
  simp [Merkle.Fold.merkleRoot, LeanImt.merkleRoot, Merkle.Fold.level, LeanImt.level, Hn,
    List.Vector.map_cons, List.Vector.head_cons] at k

/-- **Control (semantic): the bridge with the `Nat` depth one too large is false.** With the
constant hash `h _ _ = 1`, leaf 0 and depth 0, the circuit's field fold keeps the leaf (value 0) while the
`Nat` fold at depth 1 gives `(1 : Fp p).val ≠ 0`. -/
theorem control_depth_false :
    ¬ ∀ (h : Fp p → Fp p → Fp p) (leaf : Fp p) (depth : U 32) (indices : List.Vector Bool 1)
        (path : List.Vector (Fp p) 1),
      (Merkle.Fold.merkleRoot h leaf depth indices path).val =
        LeanImt.merkleRoot (Hn h) leaf.val (depth.toNat + 1) indices (path.map (·.val)) := by
  intro H
  have k := H (fun _ _ => 1) 0 0 (false ::ᵥ List.Vector.nil) (0 ::ᵥ List.Vector.nil)
  simp [Merkle.Fold.merkleRoot, LeanImt.merkleRoot, Merkle.Fold.level, LeanImt.level, Hn] at k
  exact one_ne_zero ((ZMod.val_eq_zero (1 : Fp p)).1 (by omega))

end FoldBridge.Checks
