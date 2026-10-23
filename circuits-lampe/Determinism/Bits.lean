import Determinism.Memory

/-!
Determinism of `toLeBits` at the 32-bit Boolean signature that std `to_le_bits<32>`
(inside `pow_32`, inside Poseidon's partial rounds) uses. The builtin is relational
(`f = ofDigitsLE bits`); with `2^32 < p` the 32-bit little-endian decomposition is unique.
-/

namespace Determinism
open Lampe

theorem generic_inv {A : Type} {sgn : A → List Tp × Tp} {desc} {p st argTps outTp args Q}
    (h : Builtin.genericOmni sgn desc p st argTps outTp args Q) :
    ∃ (a : A) (hA : (sgn a).fst = argTps) (hB : (sgn a).snd = outTp),
      (∃ val, desc a (hA ▸ args) val ∧ Q (some (st, hB ▸ val))) ∨
      ((∀ val, ¬ desc a (hA ▸ args) val) ∧ Q none) := by
  cases h with
  | ok hd hq => exact ⟨_, rfl, rfl, Or.inl ⟨_, hd, hq⟩⟩
  | err hn hq => exact ⟨_, rfl, rfl, Or.inr ⟨hn, hq⟩⟩

theorem bool_fin2_inj : Function.Injective (fun bit : Bool => if bit then (1 : Fin 2) else 0) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem bits_unique {p : Prime} (hp : 2 ^ 32 < p.natVal) (f : Fp p) (v₁ v₂ : List.Vector Bool 32)
    (h₁ : Builtin.toLeBitsDesc (p := p) .bool32 h![f] v₁)
    (h₂ : Builtin.toLeBitsDesc (p := p) .bool32 h![f] v₂) : v₁ = v₂ := by
  simp only [Builtin.toLeBitsDesc] at h₁ h₂
  have hc := h₁.symm.trans h₂
  have hx : RadixVec.ofDigitsLE (r := 2) (v₁.map (fun bit => if bit then (1 : Fin 2) else 0)) =
      RadixVec.ofDigitsLE (r := 2) (v₂.map (fun bit => if bit then (1 : Fin 2) else 0)) := by
    have h1 := congrArg ZMod.val hc
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_trans (RadixVec.ofDigitsLE (r := 2) (v₁.map (fun bit => if bit then (1 : Fin 2) else 0))).isLt hp),
      Nat.mod_eq_of_lt (lt_trans (RadixVec.ofDigitsLE (r := 2) (v₂.map (fun bit => if bit then (1 : Fin 2) else 0))).isLt hp)] at h1
    exact Fin.ext h1
  have hm := congrArg RadixVec.toDigitsLE hx
  rw [RadixVec.toDigitsLE_ofDigitsLE, RadixVec.toDigitsLE_ofDigitsLE] at hm
  apply List.Vector.ext
  intro i
  have := congrArg (fun v => List.Vector.get v i) hm
  simp only [List.Vector.get_map] at this
  exact bool_fin2_inj this

theorem bdet_toLeBits32 {p : Prime} (hp : 2 ^ 32 < p.natVal) :
    BDet p Builtin.toLeBits [.field] (.array .bool 32) := by
  intro st args Q₁ Q₂ h₁ h₂
  obtain ⟨a₁, hA₁, hB₁, h₁⟩ := generic_inv h₁
  obtain ⟨a₂, hA₂, hB₂, h₂⟩ := generic_inv h₂
  have ha : ∀ a : Builtin.ToLeBitsSignature,
      (Builtin.toLeBitsSgn a).snd = .array .bool 32 → a = .bool32 := by
    rintro (n | _) h
    · simp [Builtin.toLeBitsSgn] at h
    · rfl
  obtain rfl := ha a₁ hB₁
  obtain rfl := ha a₂ hB₂
  cases args with
  | cons f rest =>
    cases rest with
    | nil =>
      rcases h₁ with ⟨v₁, hd₁, hq₁⟩ | ⟨hn₁, hq₁⟩ <;> rcases h₂ with ⟨v₂, hd₂, hq₂⟩ | ⟨hn₂, hq₂⟩
      · obtain rfl := bits_unique hp f v₁ v₂ hd₁ hd₂
        exact ⟨_, hq₁, hq₂⟩
      · exact absurd hd₁ (hn₂ v₁)
      · exact absurd hd₂ (hn₁ v₂)
      · exact ⟨none, hq₁, hq₂⟩

#print axioms generic_inv
#print axioms bool_fin2_inj
#print axioms bits_unique
#print axioms bdet_toLeBits32
end Determinism
