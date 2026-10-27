import WithdrawGame.ROM.Reduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM.Control
open GameCorrespondence

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Unit
  SpendKey := Bool
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool
  derivePub := fun _ => ()
  commit := fun _ _ _ s => s
  nullify := fun _ _ => false

def note (s : Bool) : NotePlan Prim Unit := ⟨(),1,(),s⟩
def challenge : Challenge Prim Unit :=
  ⟨[.deposit (note false) (), .deposit (note true) ()], note false, note true, (), 2⟩

def classify (a b : Bool) : List (PoolGame.Event (gamePrim Prim)) → Bool
  | [.deposit _, .deposit _, .withdraw nf] => !(nf == a) && !(nf == b)
  | _ => false

/-- Query both keys in the two-element key space, at the left commitment. -/
def adversary : ROM.Adversary Prim Unit where
  State := Unit
  choose := fun _ => pure (challenge, ())
  guess := fun _ _ log => do
    let a ← liftM ((attackSpec Prim).query (.inr (.inr (false,false))))
    let b ← liftM ((attackSpec Prim).query (.inr (.inr (true,false))))
    pure (classify a b log)

theorem query_bound_two : QueryBound adversary 0 2 := by
  constructor
  · intro pk; trivial
  · intro s pk log
    simp [adversary, isQueryBoundP_query_bind_iff, charged]

theorem query_bound_zero_false : ¬QueryBound adversary 0 0 := by
  intro h
  have hg := h.2 () (fun _ => ()) []
  simp [adversary, isQueryBoundP_query_bind_iff, charged] at hg

theorem fresh (pk : Unit → Unit) : Transport.Fresh (P := Prim) pk challenge := by
  simp [Transport.Fresh, Transport.queries, challenge]

theorem run_guess (hp : Bool → Unit) (hn : (Bool × Bool) → Bool)
    (pk : Unit → Unit) (log : List (PoolGame.Event (gamePrim Prim))) :
    runAttack hp hn (adversary.guess () pk log) =
      pure (classify (hn (false,false)) (hn (true,false)) log) := by
  simp only [adversary, runAttack, simulateQ_bind, simulateQ_pure, simulateQ_query]
  rfl

theorem trace_guess (hp : Bool → Unit) (hn : (Bool × Bool) → Bool)
    (pk : Unit → Unit) (log : List (PoolGame.Event (gamePrim Prim))) :
    trace (unifFwdAnswerImpl (answers hp hn)) (adversary.guess () pk log) =
      pure (classify (hn (false,false)) (hn (true,false)) log, [false,true]) := by
  simp only [adversary]
  rfl

theorem response_eq (hp : Bool → Unit) (hn : (Bool × Bool) → Bool)
    (keys : Unit → Bool) (bit : Bool) :
    Transport.response (baseAdversary adversary hp hn) (hp ∘ keys)
      (fun x => hn (keys x.1,x.2)) challenge () bit =
      pure (bit == (!(hn (keys (),bit) == hn (false,false)) &&
        !(hn (keys (),bit) == hn (true,false)))) := by
  simp only [Transport.response, if_pos (fresh _)]
  simp only [baseAdversary, run_guess, pure_bind]
  cases bit <;> simp [classify, Transport.view,
    Transport.event, Transport.coordinate, Transport.cm, challenge, note, Prim]

theorem real_eq : realUnguarded adversary = (do
    let _hp ← $ᵗ (Bool → Unit)
    let hn ← $ᵗ ((Bool × Bool) → Bool)
    let keys ← $ᵗ (Unit → Bool)
    let bit ← $ᵗ Bool
    pure (bit == (!(hn (keys (),bit) == hn (false,false)) &&
      !(hn (keys (),bit) == hn (true,false))))) := by
  simp only [realUnguarded, Transport.test, baseAdversary, adversary, runAttack,
    simulateQ_pure, pure_bind]
  apply bind_congr; intro hp
  apply bind_congr; intro hn
  apply bind_congr; intro keys
  apply bind_congr; intro bit
  exact response_eq hp hn keys bit

abbrev Draw := ((Bool × Bool) → Bool) × (Unit → Bool) × Bool

def win (d : Draw) : Bool := d.2.2 ==
  (!(d.1 (d.2.1 (),d.2.2) == d.1 (false,false)) &&
   !(d.1 (d.2.1 (),d.2.2) == d.1 (true,false)))

theorem real_probability : Pr[= true | realUnguarded adversary] = 5/8 := by
  rw [real_eq]
  rw [probOutput_bind_of_const _ (r := 5/8)]
  · simp
  · intro hp _
    have hd : 𝒮[do
        let hn ← $ᵗ ((Bool × Bool) → Bool)
        let keys ← $ᵗ (Unit → Bool)
        let bit ← $ᵗ Bool
        pure (hn,keys,bit)] = 𝒮[$ᵗ Draw] := by
      have hi := uniform_pair (A := Unit → Bool) (B := Bool)
      calc
        _ = 𝒮[do
            let hn ← $ᵗ ((Bool × Bool) → Bool)
            let kb ← $ᵗ ((Unit → Bool) × Bool)
            pure (hn,kb)] := by
          apply evalSPMF_bind_congr_left; intro hn
          have h := congrArg (Functor.map (f := SPMF) (fun kb => (hn,kb))) hi
          simpa only [← evalSPMF_map, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using h
        _ = _ := uniform_pair
    have he : 𝒮[do
        let hn ← $ᵗ ((Bool × Bool) → Bool)
        let keys ← $ᵗ (Unit → Bool)
        let bit ← $ᵗ Bool
        pure (bit == (!(hn (keys (),bit) == hn (false,false)) &&
          !(hn (keys (),bit) == hn (true,false))))] = 𝒮[win <$> ($ᵗ Draw)] := by
      have h := congrArg (Functor.map (f := SPMF) win) hd
      simpa only [← evalSPMF_map, map_bind, map_pure, win] using h
    rw [probOutput_congr (x := true) rfl he, ← probEvent_eq_eq_probOutput,
      probEvent_map, probEvent_uniformSample]
    have hc : (Finset.univ.filter (fun d : Draw => win d = true)).card = 40 := by decide
    have ht : Fintype.card Draw = 64 := by decide
    simp only [Function.comp_def]
    change _ / _ = _
    rw [hc,ht]
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
    norm_num

noncomputable def state (hp : Bool → Unit) (hn : (Bool × Bool) → Bool)
    (keys : Unit → Bool) : St (oraclePrim Prim hp hn) :=
  (DepositData.mk ((rebaseNote hp hn (note true)).resolve keys) ()).post
    ((DepositData.mk ((rebaseNote hp hn (note false)).resolve keys) ()).post
      (St.empty (oraclePrim Prim hp hn) (fun _ => True)))

theorem legal (hp : Bool → Unit) (hn : (Bool × Bool) → Bool) (keys : Unit → Bool) :
    WithdrawGame.Legal (fun _ => True) keys (rebaseChallenge hp hn challenge) := by
  refine ⟨rfl,rfl,by change false ≠ true; decide,state hp hn keys,?_,?_,?_,?_,?_⟩
  · norm_num [RecipientGame.runChecked, RecipientGame.stepChecked, rebaseChallenge, rebaseIntent,
      challenge, rebaseNote, note, Intent.resolve, NotePlan.resolve, DepositData.guard,
      DepositData.post, St.empty, St.leaves, Note.cm, oraclePrim, Prim, U128, maxU128, state]
    intro h
    cases h
  · simp [state, DepositData.post, St.empty, rebaseChallenge, challenge]
  · simp [state, DepositData.post, St.empty, rebaseChallenge, challenge]
  all_goals norm_num [WithdrawData.guard, Challenge.withdrawal, rebaseChallenge, challenge,
    state, rebaseNote, note, DepositData.post, NotePlan.resolve, St.rootInWindow,
    St.pushWindow, rootWindow, St.empty, Note.ownedBy, St.inTreeAt, St.leaves, St.fresh,
    WithdrawData.nf, Note.nf, Note.cm, oraclePrim, Prim, U128, maxU128, bump]

theorem rejection_zero : rejectionProbability (fun _ => True) adversary = 0 := by
  simp [rejectionProbability, gameAdversary, adversary, runAttack,
    Transport.rejected_eq_not_legal, legal]

theorem control_advantage : advantage (fun _ => True) adversary = 1/8 := by
  have hd := guarded_distance (fun _ => True) adversary
  rw [rejection_zero] at hd
  unfold ProbComp.boolDistAdvantage at hd
  have he : (Pr[= true | experiment (fun _ => True) adversary]).toReal =
      (Pr[= true | realUnguarded adversary]).toReal := by
    have hz : |(Pr[= true | experiment (fun _ => True) adversary]).toReal -
        (Pr[= true | realUnguarded adversary]).toReal| = 0 := by
      apply le_antisymm (by simpa using hd) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  unfold advantage
  rw [he,real_probability]
  norm_num

theorem withdrawal_bound_zero_false :
    ¬advantage (fun _ => True) adversary ≤
      (Fintype.card Unit : ℝ) * (0 + 0) / Fintype.card Prim.SpendKey +
      (Fintype.card Unit : ℝ) * (Fintype.card Unit - 1) / Fintype.card Prim.SpendKey +
      rejectionProbability (fun _ => True) adversary / 2 := by
  rw [control_advantage,rejection_zero]
  norm_num

theorem switch_bound_zero_false : ¬OracleSwitch adversary 0 0 := by
  unfold OracleSwitch ProbComp.boolDistAdvantage
  rw [real_probability, ideal_fair (P := Prim) adversary]
  norm_num [Prim]

end LeanShieldedPool.WithdrawGame.ROM.Control
