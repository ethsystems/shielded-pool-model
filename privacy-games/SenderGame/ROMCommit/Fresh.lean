import SenderGame.ROMCommit.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROMCommit
open GameCorrespondence WithdrawGame CommitROM CommitROM.Model
variable {P : PrimSpec} {ι : Type} {cap : Nat}

def queries (pk : ι → P.PubKey) : Intent P ι → OracleComp (Spec P cap) (List (ι × P.Commitment))
  | .deposit _ _ => pure []
  | .transfer i n₁ n₂ _ _ _ => do
      let a ← Model.cm pk n₁; let b ← Model.cm pk n₂
      pure [(i,a),(i,b)]
  | .withdraw n _ _ => do let c ← Model.cm pk n; pure [(n.owner,c)]

def queryHistory (pk : ι → P.PubKey) :
    List (Intent P ι) → OracleComp (Spec P cap) (List (ι × P.Commitment))
  | [] => pure []
  | i :: is => do let qs ← queries pk i; let rest ← queryHistory pk is; pure (qs ++ rest)

def coords (pk : ι → P.PubKey) (w : SenderGame.World P ι) :
    OracleComp (Spec P cap) ((ι × P.Commitment) × (ι × P.Commitment)) := do
  let a ← Model.cm pk w.input
  let b ← Model.cm pk w.otherInput
  pure ((w.input.owner,a),(w.input.owner,b))

noncomputable def fresh (pk : ι → P.PubKey) (c : SenderGame.Challenge P ι) : OracleComp (Spec P cap) Bool := by
  classical
  exact do
    let qs ← queryHistory pk c.prior
    let l ← coords pk c.left
    let r ← coords pk c.right
    pure (decide ((l.1 ∉ qs ∧ l.2 ∉ qs ∧ l.1 ≠ l.2) ∧ (r.1 ∉ qs ∧ r.2 ∉ qs ∧ r.1 ≠ r.2)))

theorem queries_bound (pk : ι → P.PubKey) (i : Intent P ι) :
    (queries (cap := cap) pk i).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 2 := by
  cases i with
  | deposit n a => simp [queries]
  | withdraw n a s =>
    simpa only [queries, bind_pure_comp, isQueryBoundP_map_iff] using (cm_bound pk n).mono (by omega)
  | transfer i n₁ n₂ o₁ o₂ s =>
    unfold queries
    apply isQueryBoundP_bind (n := 1) (m := 1) (cm_bound pk n₁)
    intro a _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using cm_bound pk n₂

theorem queryHistory_bound (pk : ι → P.PubKey) (is : List (Intent P ι)) :
    (queryHistory (cap := cap) pk is).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) (2*is.length) := by
  induction is with
  | nil => simp [queryHistory]
  | cons i is ih =>
    simp only [queryHistory, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_comm]
    apply isQueryBoundP_bind (queries_bound pk i)
    intro qs _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

theorem coords_bound (pk : ι → P.PubKey) (w : SenderGame.World P ι) :
    (coords (cap := cap) pk w).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) 2 := by
  unfold coords
  apply isQueryBoundP_bind (n := 1) (m := 1) (cm_bound pk w.input)
  intro a _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using cm_bound pk w.otherInput

theorem fresh_bound (pk : ι → P.PubKey) (c : SenderGame.Challenge P ι) :
    (fresh (cap := cap) pk c).IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) (2*c.prior.length+4) := by
  unfold fresh
  apply isQueryBoundP_bind (n := 2*c.prior.length) (m := 4) (queryHistory_bound pk c.prior)
  intro qs _
  apply isQueryBoundP_bind (n := 2) (m := 2) (coords_bound pk c.left)
  intro l _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using coords_bound pk c.right

theorem run_queries (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (pk : ι → P.PubKey) (i : Intent P ι) :
    run (WithdrawGame.ROM.answers hp hn) hc (queries pk i) =
      pure (WithdrawGame.Transport.queries (P := commitPrim P cap hc) pk
        (rebaseIntent P.derivePub (fun x => P.nullify x.2 x.1) hc i)) := by
  have hcm (n : NotePlan P ι) := run_cm hp hn hc pk n
  simp only [run] at hcm
  cases i <;> simp only [queries, run, simulateQ_bind, simulateQ_pure, hcm, pure_bind] <;> rfl

theorem run_queryHistory (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (pk : ι → P.PubKey) (is : List (Intent P ι)) :
    run (WithdrawGame.ROM.answers hp hn) hc (queryHistory pk is) =
      pure ((is.map (rebaseIntent P.derivePub (fun x => P.nullify x.2 x.1) hc)).flatMap
        (WithdrawGame.Transport.queries (P := commitPrim P cap hc) pk)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have he := run_queries hp hn hc pk i
    simp only [run] at he ih
    simp only [queryHistory, run, simulateQ_bind, simulateQ_pure, he, ih, pure_bind]
    rfl

theorem run_coords (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (pk : ι → P.PubKey) (w : SenderGame.World P ι) :
    run (WithdrawGame.ROM.answers hp hn) hc (coords pk w) =
      pure (SenderGame.first (P := commitPrim P cap hc) pk (rebaseWorld hc w),
        SenderGame.second (P := commitPrim P cap hc) pk (rebaseWorld hc w)) := by
  have hcm (n : NotePlan P ι) := run_cm hp hn hc pk n
  simp only [run] at hcm
  simp only [coords, run, simulateQ_bind, simulateQ_pure, hcm, pure_bind]
  rfl

theorem run_fresh (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (pk : ι → P.PubKey) (c : SenderGame.Challenge P ι) :
    run (WithdrawGame.ROM.answers hp hn) hc (fresh pk c) =
      pure (by classical exact decide (SenderGame.Fresh (P := commitPrim P cap hc) pk (rebaseChallenge hc c))) := by
  classical
  have hh := run_queryHistory hp hn hc pk c.prior
  have hl := run_coords hp hn hc pk c.left
  have hr := run_coords hp hn hc pk c.right
  simp only [run] at hh hl hr
  simp only [fresh, run, simulateQ_bind, simulateQ_pure, hh, hl, hr, pure_bind]
  congr 2
  simp only [SenderGame.Fresh, Bool.forall_bool, SenderGame.Challenge.world, rebaseChallenge,
    Bool.false_eq_true, if_false, if_true]

end LeanShieldedPool.SenderGame.ROMCommit
