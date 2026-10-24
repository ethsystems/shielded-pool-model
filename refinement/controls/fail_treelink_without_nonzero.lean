-- Control (must fail to compile): the depth-0 consistency proof of `depth0_treeLink`, run on
-- the tree link without the nonzero-leaf restriction, does not elaborate: the restriction's
-- hypothesis `hne` is gone. The checked counterexample is `Toy.treeLink_needs_nonzero`.
import Refinement.Post

open LeanShieldedPool LeanShieldedPool.Refine

theorem depth0_treeLink_unrestricted (H : Nat → Nat → Nat) (G W : List Nat) :
    ∀ L, L <+: G → ∀ leaf ∈ W, Incl0 H leaf (rootOf H L) → leaf ∈ L ∨ Coll0 H L leaf := by
  intro L _ leaf _ hin
  have hl : leaf = rootOf H L := hin
  rcases L with _ | ⟨a, _ | ⟨b, t⟩⟩
  · exact absurd (hl.trans (rootOf_nil H)) hne
  · left
    rw [hl, rootOf_singleton]
    exact List.mem_singleton_self a
  · right
    refine ⟨(a :: b :: t).length, ?_, Nat.le_refl _, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [List.take_of_length_le (Nat.le_refl _)]
      exact hl
