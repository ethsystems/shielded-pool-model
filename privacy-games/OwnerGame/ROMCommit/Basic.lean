import CommitROM.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.OwnerGame.ROMCommit
open GameCorrespondence WithdrawGame CommitROM CommitROM.Model
variable {P : PrimSpec} {ι : Type} {cap : Nat}

abbrev Challenge (P : PrimSpec) (ι : Type) (cap : Nat) :=
  {c : OwnerGame.Challenge P ι // c.amount < cap}

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

def rebaseChallenge (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (c : OwnerGame.Challenge P ι) : OwnerGame.Challenge (oraclePrim P cap hp hn hc) ι :=
  ⟨c.prior.map (rebaseIntent hp hn hc),c.token,c.amount,c.funding,c.left,c.right⟩

def gameAdversary (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) :
    OwnerGame.Adversary (oraclePrim P cap hp hn hc) ι where
  State := adv.State
  choose := fun pk => do
    let (c,s) ← run (WithdrawGame.ROM.answers hp hn) hc (adv.choose pk)
    pure (rebaseChallenge hp hn hc c.val,s)
  guess := fun s pk log => run (WithdrawGame.ROM.answers hp hn) hc
    (adv.guess s pk (log.map (eventBack hp hn hc)))

def reduction (adv : Adversary P ι cap) (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    CommitROM.Adversary (Message P cap) P.Salt P.Commitment (WithdrawGame.ROM.hashSpec P) where
  State := adv.State × List (PoolGame.Event (gamePrim P))
  choose := do
    let (c,s) ← adv.choose pk
    let log ← history pk f c.val.prior
    pure ((c.val.token,⟨c.val.amount,c.property⟩,pk c.val.left),
      (c.val.token,⟨c.val.amount,c.property⟩,pk c.val.right),(s,log))
  guess := fun s cm => adv.guess s.1 pk (s.2 ++ [.deposit cm])

theorem reduction_bound (adv : Adversary P ι cap) (qc qg L : Nat)
    (hq : QueryBound adv qc qg) (hL : HistoryBound adv L)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    CommitROM.QueryBound (reduction adv pk f) (qc + 4*L) qg := by
  unfold CommitROM.QueryBound reduction
  constructor
  · apply isQueryBoundP_bind (hq.1 pk)
    intro x hx
    dsimp only
    apply (isQueryBoundP_bind (n := 4*L) (m := 0)
      ((history_bound pk f x.1.val.prior).mono (Nat.mul_le_mul_left 4 (hL pk x hx)))
      (fun _ _ => by simp)).mono (by simp)
  · intro s cm
    exact hq.2 _ _ _

theorem response_view (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (keys : ι → P.SpendKey) (c : Challenge P ι cap) (s : adv.State) (salt : P.Salt) (b : Bool) :
    OwnerGame.response (gameAdversary adv hp hn hc) keys (rebaseChallenge hp hn hc c.val) s salt b =
      (do let g ← run (WithdrawGame.ROM.answers hp hn) hc (adv.guess s (hp ∘ keys)
        (((c.val.prior.map (rebaseIntent hp hn hc)).map
          (WithdrawGame.Transport.event (P := oraclePrim P cap hp hn hc) (hp ∘ keys) (fun x => hn (keys x.1,x.2)))).map (eventBack hp hn hc) ++
            [.deposit (hc ((c.val.token,⟨c.val.amount,c.property⟩,
              hp (keys (if b then c.val.right else c.val.left))),salt))]))
          pure (b == g)) := by
  have he (i : Intent (oraclePrim P cap hp hn hc) ι) :
      gameEvent (Intent.resolve (P := oraclePrim P cap hp hn hc) keys i).event =
        WithdrawGame.Transport.event (P := oraclePrim P cap hp hn hc) (hp ∘ keys) (fun x => hn (keys x.1,x.2)) i := by
    cases i <;> rfl
  simp only [OwnerGame.response, gameAdversary, OwnerGame.Challenge.history, rebaseChallenge,
    observerView, events, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, he]
  cases b <;> simp [OwnerGame.Challenge.deposit, oraclePrim, c.property, eventBack,
    gameEvent, Tx.event, Note.cm]

noncomputable def atUnguarded [SampleableType P.Salt] [SampleableType (Model.Table P cap)]
    (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (keys : ι → P.SpendKey) : ProbComp Bool := do
  let hc ← $ᵗ (Model.Table P cap)
  let (c,s) ← run (WithdrawGame.ROM.answers hp hn) hc (adv.choose (hp ∘ keys))
  let salt ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  OwnerGame.response (gameAdversary adv hp hn hc) keys (rebaseChallenge hp hn hc c.val) s salt b

theorem reduction_eq [SampleableType P.Salt] [SampleableType (Model.Table P cap)]
    (adv : Adversary P ι cap) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (keys : ι → P.SpendKey) :
    𝒮[CommitROM.experiment (WithdrawGame.ROM.answers hp hn)
      (reduction adv (hp ∘ keys) (fun x => hn (keys x.1,x.2)))] =
        𝒮[atUnguarded adv hp hn keys] := by
  unfold CommitROM.experiment CommitROM.real atUnguarded
  rw [evalSPMF_bind_comm ($ᵗ P.Salt)]
  apply evalSPMF_bind_congr_left
  intro hc
  simp only [CommitROM.test, reduction, run, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  rw [evalSPMF_bind_comm ($ᵗ P.Salt)]
  apply evalSPMF_bind_congr_left
  intro x
  apply evalSPMF_bind_congr_left
  intro salt
  have hh := run_history hp hn hc (hp ∘ keys) (fun x => hn (keys x.1,x.2)) x.1.val.prior
  have hb := run_coins (WithdrawGame.ROM.answers hp hn) hc ($ᵗ Bool)
  unfold run at hh hb
  rw [hh, pure_bind, hb]
  apply evalSPMF_bind_congr_left
  intro b
  rw [response_view]
  cases b <;> rfl

end LeanShieldedPool.OwnerGame.ROMCommit
