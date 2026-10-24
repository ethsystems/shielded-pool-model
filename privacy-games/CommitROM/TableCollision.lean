import RecipientGame.CommitOnly.Validity

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.CommitROM

variable {I C : Type} [Finite I] [Fintype C] [Nonempty C]
  [SampleableType C] [SampleableType (I → C)]

def pairCount : Nat → Nat
  | 0 => 0
  | n+1 => n + pairCount n

theorem pairCount_twice (n : Nat) : 2 * pairCount n = n * (n-1) := by
  induction n with
  | zero => simp [pairCount]
  | succ n ih =>
    rw [pairCount]
    cases n with
    | zero => simp [pairCount]
    | succ n => simp only [Nat.add_sub_cancel] at *; nlinarith

theorem table_hit_list_le (i : I) (xs : List I) (hi : i ∉ xs) :
    Pr[fun hc : I → C => hc i ∈ xs.map hc | $ᵗ (I → C)] ≤
      (xs.length : ℝ≥0∞) / Fintype.card C := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    have hparts : i ≠ j ∧ i ∉ xs := by simpa using hi
    have hij : i ≠ j := hparts.1
    simp only [List.map_cons, List.mem_cons, List.length_cons]
    exact (probEvent_or_le _ _ _).trans ((add_le_add
      (le_of_eq (WithdrawGame.ROM.keymap_pair_collision i j hij))
      (ih hparts.2)).trans_eq (by
        simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring))

theorem table_collision_le (xs : List I) (hx : xs.Nodup) :
    Pr[fun hc : I → C => ¬(xs.map hc).Nodup | $ᵗ (I → C)] ≤
      (pairCount xs.length : ℝ≥0∞) / Fintype.card C := by
  induction xs with
  | nil => simp [pairCount]
  | cons i xs ih =>
    rw [List.nodup_cons] at hx
    simp only [List.map_cons, List.nodup_cons, not_and_or, not_not,
      List.length_cons, pairCount]
    exact (probEvent_or_le _ _ _).trans ((add_le_add
      (table_hit_list_le i xs hx.1) (ih hx.2)).trans_eq (by
        simp only [Nat.cast_add, div_eq_mul_inv]; ring))

theorem table_collision_le_real (xs : List I) (hx : xs.Nodup) :
    (Pr[fun hc : I → C => ¬(xs.map hc).Nodup | $ᵗ (I → C)]).toReal ≤
      (xs.length : ℝ) * (xs.length-1) / (2 * Fintype.card C) := by
  have hh := ENNReal.toReal_mono (by finiteness) (table_collision_le (C := C) xs hx)
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hh
  have hp : (pairCount xs.length : ℝ) * 2 = (xs.length : ℝ) * (xs.length-1) := by
    cases hlen : xs.length with
    | zero => simp [pairCount]
    | succ n =>
      have ht := pairCount_twice (n+1)
      have ht' := congrArg (fun a : Nat => (a : ℝ)) ht
      push_cast at ht'
      norm_num at ht' ⊢
      nlinarith
  calc
    _ ≤ (pairCount xs.length : ℝ) / Fintype.card C := hh
    _ = _ := by rw [← hp]; ring

end LeanShieldedPool.CommitROM
