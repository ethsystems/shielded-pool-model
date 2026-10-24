import Mathlib.Data.Nat.Basic

namespace GasEnvelope

def cap : Nat := 2 ^ 24

def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

def maxWords : Nat := 91917

def lengthBound : Nat := 32 * maxWords

def directBound : Nat := 1675621

theorem memoryCost_mono {a b : Nat} (h : a ≤ b) : memoryCost a ≤ memoryCost b := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 h)
    (Nat.div_le_div_right (Nat.mul_le_mul h h))

theorem boundary_costs :
    memoryCost maxWords = 16777186 ∧ memoryCost (maxWords + 1) = 16777548 := by
  decide

theorem memory_words_bound (a : Nat) (h : memoryCost a ≤ cap) : a ≤ maxWords := by
  by_contra hn
  have ha : maxWords + 1 ≤ a := by omega
  have hm := memoryCost_mono ha
  have hb : cap < memoryCost (maxWords + 1) := by decide
  omega

theorem memory_bytes_bound (a n : Nat) (hg : memoryCost a ≤ cap)
    (hn : n ≤ 32 * a) : n ≤ lengthBound := by
  exact le_trans hn (Nat.mul_le_mul_left 32 (memory_words_bound a hg))

theorem calldata_bytes_bound (n : Nat) (h : 21000 + 10 * n ≤ cap) : n ≤ directBound := by
  unfold cap directBound at *
  omega

theorem direct_le_memory : directBound ≤ lengthBound := by decide

theorem byte_envelope (n : Nat)
    (h : (21000 + 10 * n ≤ cap) ∨ (∃ a, memoryCost a ≤ cap ∧ n ≤ 32 * a)) :
    n ≤ lengthBound ∧ n < 2 ^ 30 := by
  have hb : n ≤ lengthBound := by
    rcases h with hd | ⟨a, hg, hn⟩
    · exact le_trans (calldata_bytes_bound n hd) direct_le_memory
    · exact memory_bytes_bound a n hg hn
  exact ⟨hb, lt_of_le_of_lt hb (by decide)⟩

theorem aggregate_memory_bytes (totalWords : Nat) (h : 3 * totalWords ≤ cap) :
    32 * totalWords ≤ 178956960 ∧ 32 * totalWords < 2 ^ 30 := by
  unfold cap at h
  omega

theorem frame_count (children : Nat) (h : 100 * children ≤ cap) :
    children ≤ 167772 ∧ children + 1 ≤ 167773 := by
  unfold cap at h
  omega

theorem aggregate_inputs (children total : Nat) (hg : 100 * children ≤ cap)
    (ht : total ≤ directBound + children * lengthBound) : total ≤ 493476841189 := by
  have hm := Nat.mul_le_mul_right lengthBound (frame_count children hg).1
  have hc : directBound + 167772 * lengthBound = 493476841189 := by decide
  omega

theorem aggregate_boundary_outputs (children total : Nat) (hg : 100 * children ≤ cap)
    (ht : total ≤ (children + 1) * lengthBound) : total ≤ 493478106912 := by
  have hm := Nat.mul_le_mul_right lengthBound (frame_count children hg).2
  have hc : 167773 * lengthBound = 493478106912 := by decide
  omega

theorem constants : cap = 16777216 ∧ lengthBound = 2941344 ∧
    lengthBound < 2 ^ 30 ∧ memoryCost (2 ^ 25) = 2199123918848 := by
  decide

#print axioms memory_words_bound
#print axioms byte_envelope
#print axioms aggregate_memory_bytes
#print axioms frame_count
#print axioms aggregate_inputs
#print axioms aggregate_boundary_outputs
#print axioms boundary_costs
#print axioms constants

end GasEnvelope
