import WithdrawGame.ROM.Queries
import VCVio.EvalDist.TVDist

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
noncomputable local instance (priority := 100000) classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Replace the selected block of a table. -/
noncomputable def program {A B R : Type} (e : A → B) (g : B → R) (f : A → R) : B → R := by
  classical
  exact fun b => if h : ∃ a, e a = b then f (Classical.choose h) else g b

theorem program_outside {A B R : Type} (e : A → B) (g : B → R) (f : A → R)
    (b : B) (h : b ∉ Set.range e) : program e g f b = g b := by
  simp only [program, Set.mem_range] at *
  exact dif_neg h

theorem program_inside {A B R : Type} {e : A → B} (he : Function.Injective e)
    (g : B → R) (f : A → R) (a : A) : program e g f (e a) = f a := by
  have hx : ∃ a', e a' = e a := ⟨a, rfl⟩
  simp only [program, dif_pos hx]
  congr 1
  exact he (Classical.choose_spec hx)

noncomputable def swapBlock {A B R : Type} (e : A → B)
    (v : (B → R) × (A → R)) : (B → R) × (A → R) :=
  (program e v.1 v.2, v.1 ∘ e)

theorem swapBlock_involutive {A B R : Type} {e : A → B} (he : Function.Injective e) :
    Function.Involutive (swapBlock (R := R) e) := by
  intro v
  apply Prod.ext
  · funext b
    change program e (program e v.1 v.2) (v.1 ∘ e) b = v.1 b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [program_inside he]
      rfl
    · rw [program_outside _ _ _ _ hb, program_outside _ _ _ _ hb]
  · funext a
    exact program_inside he v.1 v.2 a

/-- Joint block swapping preserves a uniform product table. -/
theorem swapBlock_uniform {A B R : Type} [Finite A] [Finite B] [Finite R]
    [SampleableType ((B → R) × (A → R))] {e : A → B} (he : Function.Injective e) :
    𝒮[swapBlock e <$> ($ᵗ ((B → R) × (A → R)))] =
      𝒮[$ᵗ ((B → R) × (A → R))] := by
  apply evalSPMF_ext
  intro v
  exact probOutput_map_bijective_uniformSample _ (swapBlock_involutive he).bijective v

theorem uniform_pair {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← $ᵗ A; let b ← $ᵗ B; pure (a,b)] = 𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  intro x
  simp [probOutput_bind_eq_sum_fintype, probOutput_uniformSample, Fintype.card_prod,
    ENNReal.mul_inv]

theorem program_uniform {A B R : Type} [Finite A] [Finite B] [Finite R] [Nonempty R]
    [SampleableType (B → R)] [SampleableType (A → R)]
    {e : A → B} (he : Function.Injective e) :
    𝒮[do let g ← $ᵗ (B → R); let f ← $ᵗ (A → R); pure (program e g f)] =
      𝒮[$ᵗ (B → R)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  let := Fintype.ofFinite R
  let : SampleableType R := SampleableType.ofFintype R
  have h := congrArg (Functor.map (f := SPMF) Prod.fst) (swapBlock_uniform (R := R) he)
  rw [← evalSPMF_map, ← evalSPMF_map, Functor.map_map] at h
  have hpair := uniform_pair (A := B → R) (B := A → R)
  have hp := congrArg (Functor.map (f := SPMF) (fun v => program e v.1 v.2)) hpair
  rw [← evalSPMF_map, ← evalSPMF_map] at hp
  simp only [map_bind, map_pure] at hp
  exact hp.trans (h.trans evalSPMF_map_fst_uniformSample_prod)

theorem program_bind_restrict {A B R X : Type} [Finite A] [Finite B] [Finite R]
    [Nonempty R] [SampleableType (B → R)] [SampleableType (A → R)]
    {e : A → B} (he : Function.Injective e)
    (t : (B → R) → (A → R) → ProbComp X) :
    𝒮[do let g ← $ᵗ (B → R); let f ← $ᵗ (A → R); t (program e g f) f] =
      𝒮[do let g ← $ᵗ (B → R); t g (g ∘ e)] := by
  have hr (g : B → R) (f : A → R) : program e g f ∘ e = f :=
    funext (program_inside he g f)
  calc
    _ = 𝒮[(do let g ← $ᵗ (B → R); let f ← $ᵗ (A → R); pure (program e g f)) >>=
        fun g => t g (g ∘ e)] := by simp only [bind_assoc, pure_bind, hr]
    _ = _ := by rw [evalSPMF_bind, program_uniform he, ← evalSPMF_bind]

end LeanShieldedPool.WithdrawGame.ROM
