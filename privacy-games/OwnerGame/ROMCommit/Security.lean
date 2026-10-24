import OwnerGame.ROMCommit.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.OwnerGame.ROMCommit
open GameCorrespondence WithdrawGame CommitROM CommitROM.Model
variable {P : PrimSpec} {ι : Type} {cap : Nat}

structure Draw (adv : Adversary P ι cap) where
  hp : P.SpendKey → P.PubKey
  hn : P.SpendKey × P.Commitment → P.Nullifier
  hc : Model.Table P cap
  keys : ι → P.SpendKey
  challenge : Challenge P ι cap
  state : adv.State
  salt : P.Salt
  bit : Bool

variable [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)]
  [SampleableType (Model.Table P cap)] [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]

noncomputable def draws (adv : Adversary P ι cap) : ProbComp (Draw adv) := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
  let hc ← $ᵗ (Model.Table P cap)
  let keys ← $ᵗ (ι → P.SpendKey)
  let (c,state) ← run (WithdrawGame.ROM.answers hp hn) hc (adv.choose (hp ∘ keys))
  let salt ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  pure ⟨hp,hn,hc,keys,c,state,salt,b⟩

noncomputable def experiment (sup : P.Token → Prop) (adv : Adversary P ι cap) : ProbComp Bool := do
  let d ← draws adv
  OwnerGame.challengeExp (P := oraclePrim P cap d.hp d.hn d.hc) sup
    (gameAdversary adv d.hp d.hn d.hc) d.keys
    (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.state d.salt d.bit

noncomputable def unguarded (adv : Adversary P ι cap) : ProbComp Bool := do
  let d ← draws adv
  OwnerGame.response (gameAdversary adv d.hp d.hn d.hc) d.keys
    (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.state d.salt d.bit

noncomputable def rejectionProbability (sup : P.Token → Prop) (adv : Adversary P ι cap) : ℝ := by
  classical
  exact (Pr[= true | do
    let d ← draws adv
    pure (decide (¬OwnerGame.Legal (P := oraclePrim P cap d.hp d.hn d.hc) sup d.keys
      (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.salt d.bit))]).toReal

noncomputable def advantage (sup : P.Token → Prop) (adv : Adversary P ι cap) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1/2|

/-- This game is exactly OwnerGame under the three sampled oracle tables. -/
theorem experiment_eq_owner_game (sup : P.Token → Prop) (adv : Adversary P ι cap) :
    experiment sup adv = (do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      let hc ← $ᵗ (Model.Table P cap)
      OwnerGame.experiment (P := oraclePrim P cap hp hn hc) sup (gameAdversary adv hp hn hc)) := by
  simp only [experiment, draws, OwnerGame.experiment, OwnerGame.draws, gameAdversary, bind_assoc, pure_bind]

theorem rejection_transport (sup : P.Token → Prop) (adv : Adversary P ι cap) :
    (experiment sup adv).boolDistAdvantage (unguarded adv) ≤ rejectionProbability sup adv / 2 := by
  classical
  let bad := fun d : Draw adv => decide (¬OwnerGame.Legal (P := oraclePrim P cap d.hp d.hn d.hc)
    sup d.keys (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.salt d.bit)
  let response := fun d : Draw adv => OwnerGame.response (gameAdversary adv d.hp d.hn d.hc) d.keys
    (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.state d.salt d.bit
  have he (d : Draw adv) : OwnerGame.challengeExp (P := oraclePrim P cap d.hp d.hn d.hc) sup
      (gameAdversary adv d.hp d.hn d.hc) d.keys
      (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.state d.salt d.bit =
        if bad d then $ᵗ Bool else response d := by
    by_cases h : OwnerGame.Legal (P := oraclePrim P cap d.hp d.hn d.hc) sup d.keys
      (rebaseChallenge d.hp d.hn d.hc d.challenge.val) d.salt d.bit
    · simp [bad, response, OwnerGame.challengeExp, h, OwnerGame.legal_guarded_log _ _ _ _ _ h,
        OwnerGame.response]
    · simp [bad, OwnerGame.challengeExp, h]
  have hd := RecipientGame.rejection_distance_le (draws adv) bad response
  simpa only [experiment, unguarded, rejectionProbability, he, bad, response] using hd

theorem unguarded_eq_ordered (adv : Adversary P ι cap) :
    𝒮[unguarded adv] = 𝒮[do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      let keys ← $ᵗ (ι → P.SpendKey)
      atUnguarded adv hp hn keys] := by
  simp only [unguarded, draws, atUnguarded, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr_left
  intro hp
  apply evalSPMF_bind_congr_left
  intro hn
  rw [evalSPMF_bind_comm ($ᵗ (Model.Table P cap))]

variable [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem unguarded_bias_le (adv : Adversary P ι cap) (qc qg L : Nat)
    (hq : QueryBound adv qc qg) (hL : HistoryBound adv L) :
    |(Pr[= true | unguarded adv]).toReal - 1/2| ≤ (qc + 4*L + qg : ℝ) / Fintype.card P.Salt := by
  have hb : (do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      let keys ← $ᵗ (ι → P.SpendKey)
      atUnguarded adv hp hn keys).boolDistAdvantage
    (do
      let _hp ← $ᵗ (P.SpendKey → P.PubKey)
      let _hn ← $ᵗ (P.SpendKey × P.Commitment → P.Nullifier)
      let _keys ← $ᵗ (ι → P.SpendKey)
      $ᵗ Bool) ≤ (qc + 4*L + qg : ℝ) / Fintype.card P.Salt := by
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro hp _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro hn _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro keys _
    have h := CommitROM.advantage_le_queryBound (WithdrawGame.ROM.answers hp hn)
      (reduction adv (hp ∘ keys) (fun x => hn (keys x.1,x.2))) (qc+4*L) qg
      (reduction_bound adv qc qg L hq hL _ _)
    unfold CommitROM.advantage at h
    rw [probOutput_congr (x := true) rfl (reduction_eq adv hp hn keys)] at h
    simpa [ProbComp.boolDistAdvantage, Nat.cast_add, Nat.cast_mul] using h
  rw [probOutput_congr (x := true) rfl (unguarded_eq_ordered adv)]
  simpa [ProbComp.boolDistAdvantage] using hb

/-- Deposit-owner privacy has no statistical commitment-hiding premise. -/
theorem advantage_le_queryBound (sup : P.Token → Prop) (adv : Adversary P ι cap)
    (qc qg L : Nat) (hq : QueryBound adv qc qg) (hL : HistoryBound adv L) :
    advantage sup adv ≤ (qc + 4*L + qg : ℝ) / Fintype.card P.Salt +
      rejectionProbability sup adv / 2 := by
  have hu := unguarded_bias_le adv qc qg L hq hL
  have hr := rejection_transport sup adv
  have ht := abs_sub_le (Pr[= true | experiment sup adv]).toReal
    (Pr[= true | unguarded adv]).toReal (1/2)
  unfold advantage ProbComp.boolDistAdvantage at *
  linarith

end LeanShieldedPool.OwnerGame.ROMCommit
