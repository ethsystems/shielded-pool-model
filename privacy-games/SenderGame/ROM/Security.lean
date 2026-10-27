import SenderGame.ROM.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROM
open GameCorrespondence WithdrawGame.ROM
attribute [local instance 200000] chargedDecidable
variable {P : PrimSpec} {ι : Type}
variable [Fintype ι] [Fintype P.SpendKey] [Finite P.PubKey] [Finite P.Commitment]
  [Finite P.Nullifier] [Nonempty P.SpendKey] [Nonempty P.PubKey] [Nonempty P.Nullifier]
  [SampleableType P.SpendKey] [SampleableType P.Nullifier] [SampleableType P.Salt]
  [SampleableType (ι → P.SpendKey)] [SampleableType (ι → P.PubKey)]
  [SampleableType (WithdrawGame.Transport.Table P ι)] [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]

abbrev Oracles (P : PrimSpec) :=
  (P.SpendKey → P.PubKey) × ((P.SpendKey × P.Commitment) → P.Nullifier)

noncomputable def sampleOracles : ProbComp (Oracles P) := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  pure (hp,hn)

noncomputable def experiment (sup : P.Token → Prop) (adv : Adversary P ι) : ProbComp Bool := do
  let o ← sampleOracles (P := P)
  SenderGame.experiment (P := oraclePrim P o.1 o.2) sup (gameAdversary adv o.1 o.2)

noncomputable def realUnguarded (adv : Adversary P ι) : ProbComp Bool := do
  let o ← sampleOracles (P := P)
  SenderGame.unguarded (gameAdversary adv o.1 o.2)

noncomputable def rejectionBit (sup : P.Token → Prop) (adv : Adversary P ι)
    (o : Oracles P) : ProbComp Bool := by
  classical
  exact do
    let (keys,c,_,s₁,s₂,_) ← SenderGame.draws (gameAdversary adv o.1 o.2)
    pure (decide (¬SenderGame.Legal (P := oraclePrim P o.1 o.2) sup keys c s₁ s₂))

noncomputable def rejectionProbability (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  (Pr[= true | sampleOracles (P := P) >>= rejectionBit sup adv]).toReal

noncomputable def advantage (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1/2|

theorem average_distance_le {A : Type} [Fintype A] (d : ProbComp A)
    (f g bad : A → ProbComp Bool) (c : ℝ)
    (h : ∀ a, (f a).boolDistAdvantage (g a) ≤ c * (Pr[= true | bad a]).toReal) :
    (d >>= f).boolDistAdvantage (d >>= g) ≤ c * (Pr[= true | d >>= bad]).toReal := by
  refine (PoolGame.Averaging.boolDistAdvantage_bind_le d f g).trans ?_
  rw [PoolGame.Averaging.probOutput_bind_toReal, tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hh := mul_le_mul_of_nonneg_left (h a) (show 0 ≤ (Pr[= a | d]).toReal by positivity)
  nlinarith [ENNReal.toReal_nonneg (a := Pr[= a | d])]

theorem guarded_distance (sup : P.Token → Prop) (adv : Adversary P ι) :
    (experiment sup adv).boolDistAdvantage (realUnguarded adv) ≤ rejectionProbability sup adv / 2 := by
  classical
  let := Fintype.ofFinite P.PubKey
  let := Fintype.ofFinite P.Commitment
  let := Fintype.ofFinite P.Nullifier
  have h := average_distance_le (sampleOracles (P := P))
    (fun o => SenderGame.experiment (P := oraclePrim P o.1 o.2) sup (gameAdversary adv o.1 o.2))
    (fun o => SenderGame.unguarded (gameAdversary adv o.1 o.2))
    (rejectionBit sup adv) (1/2) (fun o => by
      have hh := SenderGame.rejection_transport (P := oraclePrim P o.1 o.2) sup (gameAdversary adv o.1 o.2)
      simpa only [SenderGame.rejectionProbability, rejectionBit, div_eq_mul_inv, mul_comm, one_mul] using hh)
  simpa only [experiment, realUnguarded, rejectionProbability, div_eq_mul_inv, mul_comm, one_mul] using h

theorem unguarded_test (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) :
    SenderGame.unguarded (gameAdversary adv hp hn) = (do
      let keys ← $ᵗ (ι → P.SpendKey)
      SenderGame.test (baseAdversary adv hp hn) (hp ∘ keys) (hn ∘ keyCoord keys)) := by
  simp only [SenderGame.unguarded, SenderGame.draws, gameAdversary, bind_assoc, pure_bind,
    SenderGame.test, baseAdversary]
  apply bind_congr; intro keys
  apply bind_congr; intro x
  apply bind_congr; intro s₁
  apply bind_congr; intro s₂
  apply bind_congr; intro b
  exact rebase_response adv hp hn (hp ∘ keys) (hn ∘ keyCoord keys) x.1 x.2 s₁ s₂ b

theorem real_eq_kernel (adv : Adversary P ι) :
    𝒮[realUnguarded adv] = 𝒮[Kernel.real (test adv)] := by
  unfold Kernel.real Kernel.realAt
  simp only [realUnguarded, sampleOracles, bind_assoc, pure_bind, unguarded_test, run_test]
  rw [evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey))]
  apply evalSPMF_bind_congr_left; intro hp
  rw [evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey))]

theorem ideal_bias_le (adv : Adversary P ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hHide : OwnerGame.Hiding (P := P) ε) :
    |(Pr[= true | Kernel.ideal (test adv)]).toReal - 1/2| ≤ ε := by
  have he : 𝒮[Kernel.ideal (test adv)] = 𝒮[do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      let pk ← $ᵗ (ι → P.PubKey)
      let f ← $ᵗ (WithdrawGame.Transport.Table P ι)
      SenderGame.test (baseAdversary adv hp hn) pk f] := by
    simp only [Kernel.ideal, sampleTables, bind_assoc, pure_bind, run_test]
  rw [probOutput_congr (x := true) rfl he]
  have h : (do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      let pk ← $ᵗ (ι → P.PubKey)
      let f ← $ᵗ (WithdrawGame.Transport.Table P ι)
      SenderGame.test (baseAdversary adv hp hn) pk f).boolDistAdvantage
    (do
      let _hp ← $ᵗ (P.SpendKey → P.PubKey)
      let _hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      let _pk ← $ᵗ (ι → P.PubKey)
      $ᵗ Bool) ≤ ε := by
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const; intro hp _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const; intro hn _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const; intro pk _
    rw [PrivacyTools.distance_fair]
    exact SenderGame.ideal_test_bias_le (baseAdversary adv hp hn) pk ε hε hHide
  simpa [ProbComp.boolDistAdvantage] using h

/-- Sender privacy retains the commitment-hiding premise; the oracle switch is proved. -/
theorem advantage_le_queryBound (sup : P.Token → Prop) (adv : Adversary P ι)
    (qc qg : Nat) (hq : QueryBound adv qc qg)
    (ε : ℝ) (hε : 0 ≤ ε) (hHide : OwnerGame.Hiding (P := P) ε) :
    advantage sup adv ≤
      (Fintype.card ι : ℝ) * (qc+qg) / Fintype.card P.SpendKey +
      (Fintype.card ι : ℝ) * (Fintype.card ι-1) / Fintype.card P.SpendKey + ε +
      rejectionProbability sup adv / 2 := by
  have hs := Kernel.switch_bound (test adv) (qc+qg) (test_bound adv qc qg hq)
  have hr := guarded_distance sup adv
  have hi := ideal_bias_le adv ε hε hHide
  unfold ProbComp.boolDistAdvantage at hs hr
  rw [← probOutput_congr (x := true) rfl (real_eq_kernel adv)] at hs
  have ht := abs_sub_le (Pr[= true | experiment sup adv]).toReal
    (Pr[= true | realUnguarded adv]).toReal (1/2)
  have ht' := abs_sub_le (Pr[= true | realUnguarded adv]).toReal
    (Pr[= true | Kernel.ideal (test adv)]).toReal (1/2)
  unfold advantage
  push_cast at hs
  linarith

end LeanShieldedPool.SenderGame.ROM
