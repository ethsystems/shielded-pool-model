import SenderGame.ROMCommit.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROMCommit
open GameCorrespondence WithdrawGame.Transport
variable {P : PrimSpec} {ι : Type}

noncomputable def maskedResponse (adv : SenderGame.Adversary P ι) (pk : ι → P.PubKey)
    (f : Table P ι) (u v : P.Nullifier) (c : SenderGame.Challenge P ι) (state : adv.State)
    (s₁ s₂ : P.Salt) (b : Bool) : ProbComp Bool := by
  classical
  exact if SenderGame.Fresh pk c then do
    let w := c.world b
    let g ← adv.guess state pk (c.prior.map (event pk f) ++
      [.transfer u v (cm pk (w.out1.note s₁)) (cm pk (w.out2.note s₂))])
    pure (b == g)
  else $ᵗ Bool

variable [Finite ι] [Finite P.Commitment] [Finite P.Nullifier] [Nonempty P.Nullifier]
  [SampleableType P.Nullifier] [SampleableType P.Salt] [SampleableType (Table P ι)]

theorem response_resampled (adv : SenderGame.Adversary P ι) (pk : ι → P.PubKey)
    (c : SenderGame.Challenge P ι) (state : adv.State) (s₁ s₂ : P.Salt) (b : Bool) :
    𝒮[do let f ← $ᵗ (Table P ι); SenderGame.response adv pk f c state s₁ s₂ b] =
      𝒮[do
        let u ← $ᵗ P.Nullifier; let v ← $ᵗ P.Nullifier; let f ← $ᵗ (Table P ι)
        maskedResponse adv pk f u v c state s₁ s₂ b] := by
  classical
  by_cases hf : SenderGame.Fresh pk c
  · simp only [SenderGame.response, maskedResponse, if_pos hf]
    have he := congrArg (Functor.map (f := SPMF) (fun g => b == g))
      (SenderGame.fresh_guess_uniform adv pk c state s₁ s₂ b hf)
    simpa only [← evalSPMF_map, map_bind, map_pure, bind_pure_comp] using he
  · apply evalSPMF_ext
    intro x
    simp [SenderGame.response, maskedResponse, hf]

noncomputable def resampledTest (adv : SenderGame.Adversary P ι) (pk : ι → P.PubKey) : ProbComp Bool := do
  let u ← $ᵗ P.Nullifier
  let v ← $ᵗ P.Nullifier
  let f ← $ᵗ (Table P ι)
  let (c,state) ← adv.choose pk
  let s₁ ← $ᵗ P.Salt
  let s₂ ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  maskedResponse adv pk f u v c state s₁ s₂ b

theorem test_resampled (adv : SenderGame.Adversary P ι) (pk : ι → P.PubKey) :
    𝒮[do let f ← $ᵗ (Table P ι); SenderGame.test adv pk f] = 𝒮[resampledTest adv pk] := by
  let draws : ProbComp (SenderGame.Challenge P ι × adv.State × P.Salt × P.Salt × Bool) := do
    let (c,state) ← adv.choose pk
    let s₁ ← $ᵗ P.Salt; let s₂ ← $ᵗ P.Salt; let b ← $ᵗ Bool
    pure (c,state,s₁,s₂,b)
  let tables : ProbComp (P.Nullifier × P.Nullifier × Table P ι) := do
    let u ← $ᵗ P.Nullifier; let v ← $ᵗ P.Nullifier; let f ← $ᵗ (Table P ι)
    pure (u,v,f)
  calc
    _ = 𝒮[do let d ← draws; let f ← $ᵗ (Table P ι)
             SenderGame.response adv pk f d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2] := by
      have he := evalSPMF_bind_comm ($ᵗ (Table P ι)) draws
        (fun f d => SenderGame.response adv pk f d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2)
      simpa only [draws, SenderGame.test, bind_assoc, pure_bind] using he
    _ = 𝒮[do let d ← draws; let t ← tables
             maskedResponse adv pk t.2.2 t.1 t.2.1 d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2] := by
      apply evalSPMF_bind_congr_left
      intro d
      simpa only [tables, bind_assoc, pure_bind] using
        response_resampled adv pk d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
    _ = _ := by
      rw [evalSPMF_bind_comm draws tables]
      simp only [resampledTest, draws, tables, bind_assoc, pure_bind]

end LeanShieldedPool.SenderGame.ROMCommit
