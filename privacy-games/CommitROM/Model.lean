import CommitROM.Hiding
import SenderGame.ROM.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM.Model
open GameCorrespondence WithdrawGame WithdrawGame.Transport
variable {P : PrimSpec} {ι : Type} {cap : Nat}

/-- The finite commitment domain contains precisely the amounts below cap. -/
abbrev Message (P : PrimSpec) (cap : Nat) := P.Token × Fin cap × P.PubKey
abbrev Table (P : PrimSpec) (cap : Nat) := Message P cap × P.Salt → P.Commitment
abbrev Spec (P : PrimSpec) (cap : Nat) :=
  attackSpec (Message P cap) P.Salt P.Commitment (WithdrawGame.ROM.hashSpec P)

abbrev oraclePrim (P : PrimSpec) (cap : Nat) (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap) : PrimSpec :=
  { P with
    derivePub := hp
    nullify := fun c k => hn (k,c)
    commit := fun t a pk s => if h : a < cap then hc ((t,⟨a,h⟩,pk),s) else P.commit t a pk s }

def rebaseNote (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap) (n : NotePlan P ι) :
    NotePlan (oraclePrim P cap hp hn hc) ι := ⟨n.token,n.amount,n.owner,n.salt⟩

def rebaseIntent (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap) :
    Intent P ι → Intent (oraclePrim P cap hp hn hc) ι
  | .deposit n a => .deposit (rebaseNote hp hn hc n) a
  | .transfer i n₁ n₂ o₁ o₂ s => .transfer i
      (rebaseNote hp hn hc n₁) (rebaseNote hp hn hc n₂)
      (rebaseNote hp hn hc o₁) (rebaseNote hp hn hc o₂) s
  | .withdraw n a s => .withdraw (rebaseNote hp hn hc n) a s

def eventBack (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap) :
    PoolGame.Event (gamePrim (oraclePrim P cap hp hn hc)) → PoolGame.Event (gamePrim P)
  | .deposit cm => .deposit cm
  | .transfer a b c d => .transfer a b c d
  | .withdraw nf => .withdraw nf

def cm (pk : ι → P.PubKey) (n : NotePlan P ι) : OracleComp (Spec P cap) P.Commitment :=
  if h : n.amount < cap then
    liftM ((Spec P cap).query (.inr (.inl ((n.token,⟨n.amount,h⟩,pk n.owner),n.salt))))
  else pure (P.commit n.token n.amount (pk n.owner) n.salt)

def event (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    Intent P ι → OracleComp (Spec P cap) (PoolGame.Event (gamePrim P))
  | .deposit n _ => do let c ← cm pk n; pure (.deposit c)
  | .transfer i n₁ n₂ o₁ o₂ _ => do
      let c₁ ← cm pk n₁; let c₂ ← cm pk n₂
      let c₃ ← cm pk o₁; let c₄ ← cm pk o₂
      pure (.transfer (f (i,c₁)) (f (i,c₂)) c₃ c₄)
  | .withdraw n _ _ => do let c ← cm pk n; pure (.withdraw (f (n.owner,c)))

def history (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    List (Intent P ι) → OracleComp (Spec P cap) (List (PoolGame.Event (gamePrim P)))
  | [] => pure []
  | i :: is => do let e ← event pk f i; let es ← history pk f is; pure (e :: es)

theorem cm_bound (pk : ι → P.PubKey) (n : NotePlan P ι) :
    (cm (cap := cap) pk n).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 1 := by
  unfold cm
  split
  · simp [isQueryBoundP_query_iff, charged]
  · simp

theorem event_bound (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (i : Intent P ι) :
    (event (cap := cap) pk f i).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 4 := by
  cases i with
  | deposit n a =>
    simpa only [event, bind_pure_comp, isQueryBoundP_map_iff] using (cm_bound pk n).mono (by omega)
  | withdraw n a s =>
    simpa only [event, bind_pure_comp, isQueryBoundP_map_iff] using (cm_bound pk n).mono (by omega)
  | transfer i n₁ n₂ o₁ o₂ s =>
    unfold event
    apply isQueryBoundP_bind (n := 1) (m := 3) (cm_bound pk n₁)
    intro c₁ _
    apply isQueryBoundP_bind (n := 1) (m := 2) (cm_bound pk n₂)
    intro c₂ _
    apply isQueryBoundP_bind (n := 1) (m := 1) (cm_bound pk o₁)
    intro c₃ _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using cm_bound pk o₂

theorem history_bound (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (is : List (Intent P ι)) :
    (history (cap := cap) pk f is).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) (4 * is.length) := by
  induction is with
  | nil => simp [history]
  | cons i is ih =>
    simp only [history, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_comm]
    apply isQueryBoundP_bind (event_bound pk f i)
    intro e _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

theorem run_cm (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap)
    (pk : ι → P.PubKey) (n : NotePlan P ι) :
    run (WithdrawGame.ROM.answers hp hn) hc (cm pk n) =
      pure (WithdrawGame.Transport.cm (P := oraclePrim P cap hp hn hc) pk (rebaseNote hp hn hc n)) := by
  unfold cm
  split <;> simp only [run, simulateQ_pure, simulateQ_query]
  · simp [WithdrawGame.Transport.cm, rebaseNote, oraclePrim, *]
    rfl
  · simp [WithdrawGame.Transport.cm, rebaseNote, oraclePrim, *]

theorem run_event (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (i : Intent P ι) :
    run (WithdrawGame.ROM.answers hp hn) hc (event pk f i) =
      pure (eventBack hp hn hc (WithdrawGame.Transport.event pk f (rebaseIntent hp hn hc i))) := by
  have hb {A B : Type} (oa : OracleComp (Spec P cap) A) (k : A → OracleComp (Spec P cap) B) :
      run (WithdrawGame.ROM.answers hp hn) hc (oa >>= k) =
        run (WithdrawGame.ROM.answers hp hn) hc oa >>= fun a => run (WithdrawGame.ROM.answers hp hn) hc (k a) :=
    simulateQ_bind _ _ _
  have hpure {A : Type} (a : A) : run (WithdrawGame.ROM.answers hp hn) hc (pure a) = pure a := rfl
  cases i <;> simp only [event, hb, run_cm, pure_bind, hpure] <;> rfl

theorem run_history (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) (is : List (Intent P ι)) :
    run (WithdrawGame.ROM.answers hp hn) hc (history pk f is) =
      pure ((is.map (rebaseIntent hp hn hc)).map (WithdrawGame.Transport.event (P := oraclePrim P cap hp hn hc) pk f) |>.map (eventBack hp hn hc)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    unfold history
    have he := run_event hp hn hc pk f i
    simp only [run] at he ih
    simp only [run, simulateQ_bind, simulateQ_pure, he, ih, pure_bind]
    rfl

end LeanShieldedPool.CommitROM.Model
