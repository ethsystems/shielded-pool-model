import WithdrawGame.ROM.Bad

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
noncomputable local instance (priority := 100000) switchDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance 200000] chargedDecidable
variable {P : PrimSpec} {ι : Type}

def keyCoord (keys : ι → P.SpendKey) (x : ι × P.Commitment) : P.SpendKey × P.Commitment :=
  (keys x.1, x.2)

theorem keyCoord_injective {keys : ι → P.SpendKey} (hk : Function.Injective keys) :
    Function.Injective (keyCoord (P := P) keys) := by
  intro x y h
  apply Prod.ext
  · exact hk (congrArg Prod.fst h)
  · exact congrArg (fun z : P.SpendKey × P.Commitment => z.2) h

theorem program_answers_agree (keys : ι → P.SpendKey)
    (hp : P.SpendKey → P.PubKey) (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (pk : ι → P.PubKey) (f : Transport.Table P ι)
    (t : (attackSpec P).Domain) (ht : Avoid (Set.range keys) (queryKeys P t)) :
    unifFwdAnswerImpl (answers hp hn) t =
      unifFwdAnswerImpl (answers (program keys hp pk) (program (keyCoord keys) hn f)) t := by
  cases t with
  | inl coin => rfl
  | inr hash =>
    cases hash with
    | inl k =>
      have hk : k ∉ Set.range keys := ht k (by simp [queryKeys])
      change pure (hp k) = (pure (program keys hp pk k) : ProbComp P.PubKey)
      rw [program_outside _ _ _ _ hk]
    | inr x =>
      have hk : x.1 ∉ Set.range keys := ht x.1 (by simp [queryKeys])
      have hx : x ∉ Set.range (keyCoord keys) := by
        rintro ⟨y, hy⟩
        exact hk ⟨y.1, congrArg Prod.fst hy⟩
      change pure (hn x) = (pure (program (keyCoord keys) hn f x) : ProbComp P.Nullifier)
      rw [program_outside _ _ _ _ hx]

theorem not_avoid_range (keys : ι → P.SpendKey) (xs : List P.SpendKey) :
    (¬Avoid (Set.range keys) xs) ↔ ∃ i, keys i ∈ xs := by
  simp only [Avoid, not_forall, not_not, exists_prop, Set.mem_range]
  constructor
  · rintro ⟨k,hk,i,rfl⟩
    exact ⟨i,hk⟩
  · rintro ⟨i,hi⟩
    exact ⟨keys i,hi,i,rfl⟩

theorem programming_bound [Fintype ι] [Fintype P.SpendKey] [Nonempty P.SpendKey]
    [SampleableType P.SpendKey] [SampleableType (ι → P.SpendKey)]
    (hp : P.SpendKey → P.PubKey) (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (pk : ι → P.PubKey) (f : Transport.Table P ι)
    (oa : OracleComp (attackSpec P) Bool) (q : Nat)
    (hq : oa.IsQueryBoundP (charged P) q) :
    (do let _keys ← $ᵗ (ι → P.SpendKey); runAttack hp hn oa).boolDistAdvantage
      (do let keys ← $ᵗ (ι → P.SpendKey)
          runAttack (program keys hp pk) (program (keyCoord keys) hn f) oa) ≤
      (Fintype.card ι : ℝ) * q / Fintype.card P.SpendKey := by
  let so := unifFwdAnswerImpl (answers hp hn)
  have h := distance_bind_le_bad ($ᵗ (ι → P.SpendKey))
    (fun _ => runAttack hp hn oa)
    (fun keys => runAttack (program keys hp pk) (program (keyCoord keys) hn f) oa)
    (fun keys => do let z ← trace so oa; pure (z,keys))
    (fun z => ∃ i, z.2 i ∈ z.1.2) (fun keys => by
      have ht := distance_le_trace_hit (Set.range keys) so
        (unifFwdAnswerImpl (answers (program keys hp pk) (program (keyCoord keys) hn f)))
        (program_answers_agree keys hp hn pk f) oa
      simpa only [bind_pure_comp, probEvent_map, Function.comp_def, not_avoid_range, runAttack, so] using ht)
  have he : Pr[fun z : (Bool × List P.SpendKey) × (ι → P.SpendKey) => ∃ i, z.2 i ∈ z.1.2 |
      do let keys ← $ᵗ (ι → P.SpendKey); let z ← trace so oa; pure (z,keys)] =
      Pr[fun z => ∃ i, z.2 i ∈ z.1.2 |
      do let z ← trace so oa; let keys ← $ᵗ (ι → P.SpendKey); pure (z,keys)] := by
    simp only [probEvent_def]
    rw [evalSPMF_bind_comm]
  rw [he] at h
  have hb := ENNReal.toReal_mono (by finiteness)
    (independent_keymap_trace_hit (I := ι) so oa q hq)
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hb
  exact h.trans hb

end LeanShieldedPool.WithdrawGame.ROM
