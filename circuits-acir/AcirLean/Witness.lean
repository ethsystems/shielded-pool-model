import AcirLean.Semantics

/-!
# Concrete witnesses as binary tries (kernel-friendly lookup)

A complete binary trie of depth `d` stores the values of indices `0 .. 2^d - 1`; the bit
`d - 1` of the index selects the subtree. Values are reduced mod `P` when read, so any
stored natural number gives a canonical field element.
-/

namespace AcirLean

inductive Trie where
  | leaf (v : Nat)
  | node (l r : Trie)

def Trie.get : Trie → Nat → Nat → Nat
  | .leaf v, _, _ => v
  | .node l r, d + 1, i => if i.testBit d then r.get d i else l.get d i
  | .node _ _, 0, _ => 0

theorem P_pos : 0 < P := by decide

/-- The assignment read from a trie of depth `d`. -/
def Trie.toAssignment (t : Trie) (d : Nat) : Assignment :=
  fun i => ⟨t.get d i % P, Nat.mod_lt _ P_pos⟩

end AcirLean
