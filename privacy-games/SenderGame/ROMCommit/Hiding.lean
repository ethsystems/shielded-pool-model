import SenderGame.ROMCommit.Fresh
import SenderGame.ROMCommit.Resample

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROMCommit
open GameCorrespondence WithdrawGame CommitROM CommitROM.Model
variable {P : PrimSpec} {ι : Type} {cap : Nat}

def outputMessage (pk : ι → P.PubKey) (o : SenderGame.Output P ι) (h : o.amount < cap) : Message P cap :=
  (o.token,⟨o.amount,h⟩,pk o.owner)

noncomputable def pairReduction (adv : Adversary P ι cap) (pk : ι → P.PubKey)
    (f : WithdrawGame.Transport.Table P ι) (u v : P.Nullifier) :
    PairAdversary (Message P cap) P.Salt P.Commitment (WithdrawGame.ROM.hashSpec P) where
  State := adv.State × List (PoolGame.Event (gamePrim P)) × Bool
  choose := do
    let (c,s) ← adv.choose pk
    let log ← history pk f c.val.prior
    let ok ← fresh pk c.val
    pure ((outputMessage pk (c.val.world false).out1 (c.property false).1,
           outputMessage pk (c.val.world true).out1 (c.property true).1),
          (outputMessage pk (c.val.world false).out2 (c.property false).2,
           outputMessage pk (c.val.world true).out2 (c.property true).2),
          (s,log,ok))
  guess := fun s c₁ c₂ => if s.2.2 then
    adv.guess s.1 pk (s.2.1 ++ [.transfer u v c₁ c₂])
    else liftComp ($ᵗ Bool) (Spec P cap)

theorem pairReduction_bound (adv : Adversary P ι cap) (qc qg L : Nat)
    (hq : QueryBound adv qc qg) (hL : HistoryBound adv L)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (u v : P.Nullifier) :
    PairQueryBound (pairReduction adv pk f u v) (qc+6*L+4) qg := by
  unfold PairQueryBound pairReduction
  constructor
  · apply (isQueryBoundP_bind (n := qc) (m := 4*L+(2*L+4)) (hq.1 pk) ?_).mono (by omega)
    intro x hx
    apply isQueryBoundP_bind (n := 4*L) (m := 2*L+4)
      ((history_bound pk f x.1.val.prior).mono (Nat.mul_le_mul_left 4 (hL pk x hx)))
    intro log _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      (fresh_bound pk x.1.val).mono (by have h := hL pk x hx; omega)
  · intro s c₁ c₂
    dsimp only
    split
    · exact hq.2 _ _ _
    · exact coins_bound _ _

theorem run_history_commit (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (is : List (Intent P ι)) :
    run (WithdrawGame.ROM.answers hp hn) hc (history pk f is) =
      pure (((is.map (rebaseIntent P.derivePub (fun x => P.nullify x.2 x.1) hc)).map
        (WithdrawGame.Transport.event (P := commitPrim P cap hc) pk f)).map (back hc)) := by
  rw [run_history hp hn hc pk f is]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  cases i <;> rfl

theorem fair_win (b : Bool) : 𝒮[do let g ← $ᵗ Bool; pure (b == g)] = 𝒮[$ᵗ Bool] := by
  apply evalSPMF_ext
  intro x
  cases b <;> cases x <;> simp

variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

theorem pairReduction_eq (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (pk : ι → P.PubKey)
    (f : WithdrawGame.Transport.Table P ι) (u v : P.Nullifier) :
    𝒮[pairExperiment (WithdrawGame.ROM.answers hp hn) (pairReduction adv pk f u v)] =
      𝒮[do
        let hc ← $ᵗ (Model.Table P cap)
        let (c,state) ← run (WithdrawGame.ROM.answers hp hn) hc (adv.choose pk)
        let s₁ ← $ᵗ P.Salt; let s₂ ← $ᵗ P.Salt; let b ← $ᵗ Bool
        maskedResponse (baseAdversary adv hp hn hc) pk f u v
          (rebaseChallenge hc c.val) state s₁ s₂ b] := by
  classical
  unfold pairExperiment pairReduction
  apply evalSPMF_bind_congr_left
  intro hc
  have hh (is : List (Intent P ι)) := run_history_commit hp hn hc pk f is
  have hf (c : SenderGame.Challenge P ι) := run_fresh hp hn hc pk c
  simp only [run] at hh hf
  simp only [run, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, hh, hf]
  apply evalSPMF_bind_congr_left
  intro x
  apply evalSPMF_bind_congr_left
  intro s₁
  apply evalSPMF_bind_congr_left
  intro s₂
  apply evalSPMF_bind_congr_left
  intro b
  by_cases h : SenderGame.Fresh (P := commitPrim P cap hc) pk (rebaseChallenge hc x.1.val)
  · simp only [h, decide_true, if_true, maskedResponse]
    have ho (o : SenderGame.Output P ι) (ho : o.amount < cap) (s : P.Salt) :
        WithdrawGame.Transport.cm (P := commitPrim P cap hc) pk ((rebaseOutput hc o).note s) =
          hc (outputMessage pk o ho,s) := by
      simp [WithdrawGame.Transport.cm, rebaseOutput, SenderGame.Output.note, outputMessage, commitPrim, oraclePrim, ho]
    have hlf := (x.1.property false).1
    have hls := (x.1.property false).2
    have hrf := (x.1.property true).1
    have hrs := (x.1.property true).2
    simp only [SenderGame.Challenge.world, Bool.false_eq_true, if_false, if_true] at hlf hls hrf hrs
    cases b <;>
      simp [baseAdversary, SenderGame.Challenge.world, rebaseChallenge, rebaseWorld, back,
        eventBack, List.map_append, ho, hlf, hls, hrf, hrs, run, Function.comp_def]
  · simp only [h, decide_false, Bool.false_eq_true, if_false, maskedResponse]
    have hc := run_coins (WithdrawGame.ROM.answers hp hn) hc ($ᵗ Bool)
    unfold run at hc
    rw [hc]
    exact fair_win b

variable [Finite ι] [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]
  [Finite P.Nullifier] [Nonempty P.Nullifier] [SampleableType P.Nullifier]
  [SampleableType (WithdrawGame.Transport.Table P ι)]

theorem idealAt_bias_le (adv : Adversary P ι cap) (qc qg L : Nat)
    (hq : QueryBound adv qc qg) (hL : HistoryBound adv L)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (pk : ι → P.PubKey) :
    |(Pr[= true | do
      let hc ← $ᵗ (Model.Table P cap)
      let f ← $ᵗ (WithdrawGame.Transport.Table P ι)
      SenderGame.test (baseAdversary adv hp hn hc) pk f]).toReal - 1/2| ≤
        (2*(qc+6*L+4+qg)+1 : ℝ) / Fintype.card P.Salt := by
  let masks : ProbComp (P.Nullifier × P.Nullifier × WithdrawGame.Transport.Table P ι) := do
    let u ← $ᵗ P.Nullifier; let v ← $ᵗ P.Nullifier; let f ← $ᵗ (WithdrawGame.Transport.Table P ι)
    pure (u,v,f)
  have he : 𝒮[do
      let hc ← $ᵗ (Model.Table P cap)
      let f ← $ᵗ (WithdrawGame.Transport.Table P ι)
      SenderGame.test (baseAdversary adv hp hn hc) pk f] =
      𝒮[do let t ← masks; pairExperiment (WithdrawGame.ROM.answers hp hn) (pairReduction adv pk t.2.2 t.1 t.2.1)] := by
    calc
      _ = 𝒮[do let hc ← $ᵗ (Model.Table P cap); resampledTest (baseAdversary adv hp hn hc) pk] := by
        apply evalSPMF_bind_congr_left
        intro hc
        exact test_resampled (P := commitPrim P cap hc) (baseAdversary adv hp hn hc) pk
      _ = _ := by
        have hs := evalSPMF_bind_comm ($ᵗ (Model.Table P cap)) masks
          (fun hc t => do
            let (c,state) ← run (WithdrawGame.ROM.answers hp hn) hc (adv.choose pk)
            let s₁ ← $ᵗ P.Salt; let s₂ ← $ᵗ P.Salt; let b ← $ᵗ Bool
            maskedResponse (baseAdversary adv hp hn hc) pk t.2.2 t.1 t.2.1
              (rebaseChallenge hc c.val) state s₁ s₂ b)
        simp only [masks, resampledTest, baseAdversary, bind_assoc, pure_bind] at hs ⊢
        rw [hs]
        apply evalSPMF_bind_congr_left
        intro u
        apply evalSPMF_bind_congr_left
        intro v
        apply evalSPMF_bind_congr_left
        intro f
        exact (pairReduction_eq adv hp hn pk f u v).symm
  rw [probOutput_congr (x := true) rfl he]
  have hb := PoolGame.Averaging.boolDistAdvantage_bind_le_const masks
    (fun t => pairExperiment (WithdrawGame.ROM.answers hp hn) (pairReduction adv pk t.2.2 t.1 t.2.1))
    (fun _ => $ᵗ Bool) ((2*(qc+6*L+4+qg)+1 : ℝ) / Fintype.card P.Salt) (by
      intro t _
      rw [PrivacyTools.distance_fair]
      have h := pair_advantage_le_queryBound (WithdrawGame.ROM.answers hp hn)
        (pairReduction adv pk t.2.2 t.1 t.2.1) (qc+6*L+4) qg
        (pairReduction_bound adv qc qg L hq hL _ _ _ _)
      simpa [Nat.cast_add, Nat.cast_mul] using h)
  simpa [ProbComp.boolDistAdvantage] using hb

end LeanShieldedPool.SenderGame.ROMCommit
