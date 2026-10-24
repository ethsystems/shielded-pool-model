import CommitROM.Lower
import CommitROM.Pair
import SenderGame.ROM.Security

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROMCommit
open GameCorrespondence WithdrawGame CommitROM CommitROM.Model
variable {P : PrimSpec} {ι : Type} {cap : Nat}

abbrev Challenge (P : PrimSpec) (ι : Type) (cap : Nat) :=
  {c : SenderGame.Challenge P ι // ∀ b, (c.world b).out1.amount < cap ∧ (c.world b).out2.amount < cap}

structure Adversary (P : PrimSpec) (ι : Type) (cap : Nat) where
  State : Type
  choose : (ι → P.PubKey) → OracleComp (Spec P cap) (Challenge P ι cap × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) → OracleComp (Spec P cap) Bool

def QueryBound (adv : Adversary P ι cap) (qc qg : Nat) : Prop :=
  (∀ pk, (adv.choose pk).IsQueryBoundP
    (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) qc) ∧
  ∀ s pk log, (adv.guess s pk log).IsQueryBoundP
    (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) qg

def HistoryBound (adv : Adversary P ι cap) (L : Nat) : Prop :=
  ∀ pk x, x ∈ support (adv.choose pk) → x.1.val.prior.length ≤ L

def rebaseOutput (hc : Model.Table P cap) (o : SenderGame.Output P ι) :
    SenderGame.Output (commitPrim P cap hc) ι := ⟨o.token,o.amount,o.owner⟩

def rebaseWorld (hc : Model.Table P cap) (w : SenderGame.World P ι) :
    SenderGame.World (commitPrim P cap hc) ι :=
  ⟨rebaseNote P.derivePub (fun x => P.nullify x.2 x.1) hc w.input,
    rebaseNote P.derivePub (fun x => P.nullify x.2 x.1) hc w.otherInput,
    rebaseOutput hc w.out1,rebaseOutput hc w.out2⟩

def rebaseChallenge (hc : Model.Table P cap) (c : SenderGame.Challenge P ι) :
    SenderGame.Challenge (commitPrim P cap hc) ι :=
  ⟨c.prior.map (rebaseIntent P.derivePub (fun x => P.nullify x.2 x.1) hc),
    rebaseWorld hc c.left,rebaseWorld hc c.right,c.snapshot⟩

def back (hc : Model.Table P cap) := eventBack P.derivePub (fun x => P.nullify x.2 x.1) hc

def lowerAdversary (adv : Adversary P ι cap) (hc : Model.Table P cap) :
    SenderGame.ROM.Adversary (commitPrim P cap hc) ι where
  State := adv.State
  choose := fun pk => do
    let (c,s) ← lower (P := P) hc (adv.choose pk)
    pure (rebaseChallenge hc c.val,s)
  guess := fun s pk log => lower (P := P) hc (adv.guess s pk (log.map (back hc)))

theorem lowerAdversary_bound (adv : Adversary P ι cap) (hc : Model.Table P cap)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    SenderGame.ROM.QueryBound (lowerAdversary adv hc) qc qg := by
  unfold SenderGame.ROM.QueryBound lowerAdversary
  have hcq : WithdrawGame.ROM.charged (commitPrim P cap hc) = WithdrawGame.ROM.charged P := by
    funext t
    cases t <;> rfl
  simp only [hcq]
  constructor
  · intro pk
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using lower_bound (P := P) hc _ qc (hq.1 pk)
  · intro s pk log
    exact lower_bound (P := P) hc _ qg (hq.2 s pk (log.map (back hc)))

def baseAdversary (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    SenderGame.Adversary (commitPrim P cap hc) ι where
  State := adv.State
  choose := fun pk => do
    let (c,s) ← run (WithdrawGame.ROM.answers (P := P) hp hn) hc (adv.choose pk)
    pure (rebaseChallenge hc c.val,s)
  guess := fun s pk log => run (WithdrawGame.ROM.answers (P := P) hp hn) hc (adv.guess s pk (log.map (back hc)))

theorem baseAdversary_eq (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    SenderGame.ROM.baseAdversary (lowerAdversary adv hc) hp hn = baseAdversary adv hp hn hc := by
  unfold SenderGame.ROM.baseAdversary lowerAdversary baseAdversary
  simp only [WithdrawGame.ROM.runAttack, simulateQ_bind, simulateQ_pure]
  congr 1
  · funext pk
    convert congrArg (fun oa => oa >>= fun x => pure (rebaseChallenge hc x.1.val,x.2))
      (run_lower (P := P) hp hn hc (adv.choose pk)) using 1
    rfl
  · funext s pk log
    convert run_lower (P := P) hp hn hc (adv.guess s pk (log.map (back hc))) using 1
    rfl

noncomputable def experiment [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)]
    [SampleableType (Model.Table P cap)]
    (sup : P.Token → Prop) (adv : Adversary P ι cap) : ProbComp Bool := do
  let hc ← $ᵗ (Model.Table P cap)
  SenderGame.ROM.experiment (P := commitPrim P cap hc) sup (lowerAdversary adv hc)

noncomputable def unguarded [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)]
    [SampleableType (Model.Table P cap)] (adv : Adversary P ι cap) : ProbComp Bool := do
  let hc ← $ᵗ (Model.Table P cap)
  SenderGame.ROM.realUnguarded (lowerAdversary adv hc)

noncomputable def rejectionProbability [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)]
    [SampleableType (Model.Table P cap)] (sup : P.Token → Prop) (adv : Adversary P ι cap) : ℝ :=
  (Pr[= true | do
    let hc ← $ᵗ (Model.Table P cap)
    SenderGame.ROM.sampleOracles (P := commitPrim P cap hc) >>=
      SenderGame.ROM.rejectionBit sup (lowerAdversary adv hc)]).toReal

noncomputable def advantage [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType (P.SpendKey × P.Commitment → P.Nullifier)]
    [SampleableType (Model.Table P cap)] (sup : P.Token → Prop) (adv : Adversary P ι cap) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1/2|

end LeanShieldedPool.SenderGame.ROMCommit
