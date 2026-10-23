import Determinism.DepositHash
/-! Must-fail control: `bdet_toLeBits32` without `2^32 < p` (proof unchanged except that
the hypothesis is gone). -/
namespace Controls.DepositHash
open Lampe Determinism
theorem toLeBits_det_without_bound {p : Prime} :
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
      · obtain rfl := bits_unique (by assumption) f v₁ v₂ hd₁ hd₂
        exact ⟨_, hq₁, hq₂⟩
      · exact absurd hd₁ (hn₂ v₁)
      · exact absurd hd₂ (hn₁ v₂)
      · exact ⟨none, hq₁, hq₂⟩
end Controls.DepositHash
