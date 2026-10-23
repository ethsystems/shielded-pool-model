import Exec.Heap
import Exec.ArrayOps

/-!
The extracted `binary_merkle_root<N>` as a pure fold.

`merkleRoot h leaf depth indices path` folds `level` over the positions `0 .. N-1`, as the
extracted loop does. At position `i < depth` the node is hashed with `path[i]`; the direction bit
`indices[i] = false` puts the node on the LEFT (`h node path[i]`), `true` on the right
(`h path[i] node`), as the extracted `if !indices[i] { (node, sibling) } else { (sibling, node) }`.
Positions `i ≥ depth` keep the node (the extracted `if i < depth` has no else branch).

`bmr_fwd` is the forward result for the extracted declaration, for every `N`, depth, leaf, path
and direction bits, with any hasher that has a forward result `h`. The loop invariant is the value
of the `node` reference (`Exec.Loop.loop_inv`); Lampe's frame rule (`Omni.frame`) keeps that
reference through each hasher call. No claim about Poseidon's cryptographic properties.
-/

namespace Merkle.Fold
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

section
variable {p : Prime}

/-- One iteration of the extracted loop at position `i`. -/
def level (h : Fp p → Fp p → Fp p) (depth : ℕ) (indices : List Bool) (path : List (Fp p))
    (node : Fp p) (i : ℕ) : Fp p :=
  if i < depth then
    if indices.getD i false then h (path.getD i 0) node else h node (path.getD i 0)
  else node

/-- The extracted `binary_merkle_root<n>` as a fold over the positions `0 .. n-1`. -/
def merkleRoot {n : ℕ} (h : Fp p → Fp p → Fp p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool n) (path : List.Vector (Fp p) n) : Fp p :=
  (List.range n).foldl (level h depth.toNat indices.toList path.toList) leaf

/-- A call with a forward result keeps every existing heap cell (Lampe's frame rule, applied to the
forward result from the empty state). -/
theorem keep_lookup {Γ tp} {e : Expr (Tp.denote p) tp} {v : Tp.denote p tp}
    (hfwd : ∀ st, Omni p Γ st e (fun r => ∃ st', r = some (st', v)))
    (st : State p) (addr : Address) (c : AnyValue p) (hc : st.vals.lookup addr = some c) :
    Omni p Γ st e (fun r => ∃ st', r = some (st', v) ∧ st'.vals.lookup addr = some c) := by
  have h := Omni.frame (st₁ := ⟨∅, ∅⟩) (st₂ := st) (hfwd ⟨∅, ∅⟩)
    ⟨Finmap.disjoint_empty _, Finmap.disjoint_empty _⟩
  have he : ((⟨∅, ∅⟩ : State p) ∪ st) = st := by
    cases st
    simp only [State.union_parts, Finmap.empty_union]
  rw [he] at h
  refine Omni.consequence h ?_
  rintro (_ | ⟨st', v'⟩) hr
  · obtain ⟨_, h⟩ := hr; cases h
  · obtain ⟨s₁, s₂, hd, rfl, ⟨s₁', hs⟩, rfl⟩ := hr
    cases hs
    refine ⟨_, rfl, ?_⟩
    have hmem : addr ∈ s₂.vals := Finmap.mem_of_lookup_eq_some hc
    have hnot : addr ∉ s₁.vals := fun h1 => hd.1 addr h1 hmem
    rw [State.union_vals, Finmap.lookup_union_right hnot]
    exact hc

theorem ult_true {Γ st} {i d : U 32} (h : i < d) :
    Omni p Γ st (.callBuiltin [.u 32, .u 32] .bool Builtin.uLt h![i, d]) (fun r => r = some (st, true)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := 32) True.intro (by simp [h]; rfl)

theorem ult_false {Γ st} {i d : U 32} (h : ¬ i < d) :
    Omni p Γ st (.callBuiltin [.u 32, .u 32] .bool Builtin.uLt h![i, d]) (fun r => r = some (st, false)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := 32) True.intro (by simp [h]; rfl)

theorem uleq_true {Γ st} {i d : U 32} (h : i ≤ d) :
    Omni p Γ st (.callBuiltin [.u 32, .u 32] .bool Builtin.uLeq h![i, d]) (fun r => r = some (st, true)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := 32) True.intro (by simp [h]; rfl)

theorem bnot_val {Γ st} (b : Bool) :
    Omni p Γ st (.callBuiltin [.bool] .bool Builtin.bNot h![b]) (fun r => r = some (st, !b)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

theorem make_pair {Γ st} (x y : Fp p) :
    Omni p Γ st (.callBuiltin [.field, .field] (.tuple none [.field, .field]) Builtin.makeData h![x, y])
      (fun r => r = some (st, HList.toTuple p h![x, y] none)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ((none : Option String), [Tp.field, Tp.field])) True.intro rfl

theorem head_pair {Γ st} (x y : Fp p) :
    Omni p Γ st (.callBuiltin [.tuple none [.field, .field] ] .field (Builtin.getMember (Member.head : Member .field [.field, .field]))
      h![HList.toTuple p h![x, y] none]) (fun r => r = some (st, x)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := (none : Option String)) True.intro rfl

theorem tail_pair {Γ st} (x y : Fp p) :
    Omni p Γ st (.callBuiltin [.tuple none [.field, .field] ] .field (Builtin.getMember (Member.head.tail : Member .field [.field, .field]))
      h![HList.toTuple p h![x, y] none]) (fun r => r = some (st, y)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := (none : Option String)) True.intro rfl

theorem mk_pair {Γ st} (x y : Fp p) :
    Omni p Γ st (.callBuiltin [.field, .field] (.array .field 2) Builtin.mkArray h![x, y])
      (fun r => r = some (st, (⟨[x, y], rfl⟩ : List.Vector (Fp p) 2))) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ((2 : U 32), Tp.field)) True.intro rfl

theorem vget_getD {α : Type} {n : ℕ} (v : List.Vector α n) (k : ℕ) (hk : k < n) (d : α) :
    v.toList.getD k d = v.get ⟨k, hk⟩ := by
  obtain ⟨l, hl⟩ := v
  subst hl
  simp [List.Vector.get, List.getElem?_eq_getElem hk]

theorem fold_succ (h : Fp p → Fp p → Fp p) (depth : ℕ) (indices : List Bool) (path : List (Fp p))
    (leaf : Fp p) (k : ℕ) :
    (List.range (k+1)).foldl (level h depth indices path) leaf =
      level h depth indices path ((List.range k).foldl (level h depth indices path) leaf) k := by
  rw [List.range_succ, List.foldl_append]; rfl

theorem succ_toNat {i N : U 32} (h : i < N) : (i + 1).toNat = i.toNat + 1 := by
  have hlt : i.toNat < N.toNat := h
  have hh := N.isLt
  have hw : 1 < 2^32 := by decide
  change (i.toNat + 1 % 2^32) % 2^32 = i.toNat + 1
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]

/-- Forward result for the extracted `binary_merkle_root<N>` with a hasher that computes `h`:
it returns `merkleRoot h leaf depth indices path`, for every depth. -/
theorem bmr_fwd {Γ : Env} (N : U 32) (h : Fp p → Fp p → Fp p) (hasher : FuncRef [.array .field 2] .field)
    (hmem : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ Γ.functions)
    (hfwd : ∀ st (a b : Fp p), Omni p Γ st (Expr.call [.array .field 2] .field hasher
      h![(⟨[a, b], rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', h a b)))
    (st : State p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool N.toNat) (path : List.Vector (Fp p) N.toNat) :
    Omni p Γ st («binary_merkle_root-0.0.0::binary_merkle_root».call h![N]
        h![hasher, leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', merkleRoot h leaf depth indices path)) := by
  apply call _ _ _ hmem
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  apply bind_ref; intro addr hfresh
  exec_pure
  exec_pure
  apply Omni.letIn (Exec.Loop.loop_inv _ N _
    (fun i s => s.vals.lookup addr =
      some ⟨.field, (List.range i.toNat).foldl (level h depth.toNat indices.toList path.toList) leaf⟩)
    ?step (by simp [BitVec.le_def]) ?init)
  case init =>
    rw [Finmap.lookup_insert]; rfl
  case step =>
    intro i s hil hih hinv
    by_cases hd : i < depth
    · apply bind_value (ult_true hd)
      apply Omni.iteTrue
      apply bind_value (Exec.ArrayOps.cast32 i)
      apply bind_value (Exec.ArrayOps.index (tp := .field) (n := N) path i hih)
      apply bind_value (Exec.ArrayOps.cast32 i)
      apply bind_value (Exec.ArrayOps.index (tp := .bool) (n := N) indices i hih)
      generalize hb : indices.get ⟨i.toNat, hih⟩ = b
      apply bind_value (bnot_val b)
      cases b
      · -- indices[i] = false: the node is the left input
        refine bind_value (st' := s) (v := ?tv) ?h1 ?h2
        case h1 =>
          apply Omni.iteTrue
          apply bind_read hinv
          exact make_pair _ _
        case h2 =>
          apply bind_value (head_pair _ _)
          apply bind_value (tail_pair _ _)
          apply bind_value (mk_pair _ _)
          apply Omni.letIn (keep_lookup (fun st => hfwd st _ _) s addr _ hinv)
          · rintro _ _ ⟨s', heq, hl⟩
            cases heq
            apply Omni.letIn (Exec.Heap.write _ addr _ _ hl)
            · rintro _ _ ⟨s'', heq, hl', -⟩
              cases heq
              apply Omni.skip
              refine ⟨_, rfl, ?_⟩
              rw [hl', succ_toNat hih, fold_succ]
              simp only [level, show i.toNat < depth.toNat from hd, if_true,
                vget_getD indices _ hih, vget_getD path _ hih, hb, Bool.false_eq_true, if_false]
              rfl
            · rintro ⟨_, h, _⟩; cases h
          · rintro ⟨_, h, _⟩; cases h
      · -- indices[i] = true: the node is the right input
        refine bind_value (st' := s) (v := ?tvR) ?h1R ?h2R
        case h1R =>
          apply Omni.iteFalse
          apply bind_read hinv
          exact make_pair _ _
        case h2R =>
          apply bind_value (head_pair _ _)
          apply bind_value (tail_pair _ _)
          apply bind_value (mk_pair _ _)
          apply Omni.letIn (keep_lookup (fun st => hfwd st _ _) s addr _ hinv)
          · rintro _ _ ⟨s', heq, hl⟩
            cases heq
            apply Omni.letIn (Exec.Heap.write _ addr _ _ hl)
            · rintro _ _ ⟨s'', heq, hl', -⟩
              cases heq
              apply Omni.skip
              refine ⟨_, rfl, ?_⟩
              rw [hl', succ_toNat hih, fold_succ]
              simp only [level, show i.toNat < depth.toNat from hd, if_true,
                vget_getD indices _ hih, vget_getD path _ hih, hb, if_true]
              rfl
            · rintro ⟨_, h, _⟩; cases h
          · rintro ⟨_, h, _⟩; cases h
    · apply bind_value (ult_false hd)
      apply Omni.iteFalse
      apply Omni.skip
      refine ⟨s, rfl, ?_⟩
      rw [succ_toNat hih, fold_succ, hinv]
      simp only [level, show ¬ i.toNat < depth.toNat from hd, if_false]
  · rintro _ s' ⟨s'', heq, hinv⟩
    cases heq
    apply Omni.callBuiltin
    apply Builtin.readRefOmni.mk hinv
    exact ⟨_, rfl⟩
  · rintro ⟨_, h, _⟩; cases h

/-- A reading check of the conventions, for an abstract hasher: at depth 2 of 3, position 0 has
direction bit `true` (node on the right), position 1 has `false` (node on the left), and
position 2 is inactive although its bit is `true`. -/
theorem merkleRoot_example (h : Fp p → Fp p → Fp p) (leaf a b c : Fp p) :
    merkleRoot h leaf (2 : U 32) (⟨[true, false, true], rfl⟩ : List.Vector Bool 3)
      (⟨[a, b, c], rfl⟩ : List.Vector (Fp p) 3) = h (h a leaf) b := by
  rfl

/-- Depth 0: every position is inactive and the root is the leaf. -/
theorem merkleRoot_depth0 {n : ℕ} (h : Fp p → Fp p → Fp p) (leaf : Fp p)
    (indices : List.Vector Bool n) (path : List.Vector (Fp p) n) :
    merkleRoot h leaf (0 : U 32) indices path = leaf := by
  unfold merkleRoot
  generalize List.range n = l
  induction l generalizing leaf with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons, level, BitVec.toNat_zero, Nat.not_lt_zero, if_false]
    exact ih leaf

end

#print axioms merkleRoot_example
#print axioms merkleRoot_depth0
#print axioms level
#print axioms merkleRoot
#print axioms keep_lookup
#print axioms ult_true
#print axioms ult_false
#print axioms uleq_true
#print axioms bnot_val
#print axioms make_pair
#print axioms head_pair
#print axioms tail_pair
#print axioms mk_pair
#print axioms vget_getD
#print axioms fold_succ
#print axioms succ_toNat
#print axioms bmr_fwd
end Merkle.Fold
