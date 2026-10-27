import CommitROM.Pair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM.Control
abbrev Aux := (Unit →ₒ Unit) + (Unit →ₒ Unit)
def other : QueryImpl Aux Id := QueryImpl.ofFn (fun _ => ()) + QueryImpl.ofFn (fun _ => ())

def adversary : Adversary Bool Bool Bool Aux where
  State := Unit
  choose := pure (false,true,())
  guess := fun _ cm => do
    let a ← liftM ((attackSpec Bool Bool Bool Aux).query (.inr (.inl (false,false))))
    let b ← liftM ((attackSpec Bool Bool Bool Aux).query (.inr (.inl (false,true))))
    pure (!(a == cm) && !(b == cm))

theorem query_bound_two : QueryBound adversary 0 2 := by
  constructor
  · trivial
  · intro s cm
    simp [adversary, isQueryBoundP_query_bind_iff, charged]

theorem query_bound_zero_false : ¬QueryBound adversary 0 0 := by
  intro h
  have hh := h.2 () false
  simp [adversary, isQueryBoundP_query_bind_iff, charged] at hh

theorem trace_queries (h : Bool × Bool → Bool) (cm : Bool) :
    trace (unifFwdAnswerImpl (QueryImpl.ofFn h + other)) (adversary.guess () cm) =
      pure (!(h (false,false) == cm) && !(h (false,true) == cm), [false,true]) := by
  rfl

theorem challenge_salt_queried (salt : Bool) : salt ∈ [false,true] := by cases salt <;> simp

abbrev Draw := (Bool × Bool → Bool) × Bool × Bool
def win (d : Draw) : Bool := d.2.2 ==
  (!(d.1 (false,false) == d.1 (d.2.2,d.2.1)) && !(d.1 (false,true) == d.1 (d.2.2,d.2.1)))

theorem experiment_eq : 𝒮[experiment other adversary] = 𝒮[win <$> ($ᵗ Draw)] := by
  have he : 𝒮[experiment other adversary] = 𝒮[do
      let h ← $ᵗ (Bool × Bool → Bool)
      let s ← $ᵗ Bool
      let b ← $ᵗ Bool
      pure (win (h,s,b))] := by
    unfold experiment real test
    rw [evalSPMF_bind_comm ($ᵗ Bool)]
    apply evalSPMF_bind_congr_left
    intro h
    apply evalSPMF_bind_congr_left
    intro s
    simp only [adversary, run, simulateQ_bind, simulateQ_pure, pure_bind]
    have hb := run_coins other h ($ᵗ Bool)
    unfold run at hb
    rw [hb]
    apply evalSPMF_bind_congr_left
    intro b
    cases b <;> rfl
  have hd : 𝒮[do
      let h ← $ᵗ (Bool × Bool → Bool)
      let s ← $ᵗ Bool; let b ← $ᵗ Bool; pure (h,s,b)] = 𝒮[$ᵗ Draw] := by
    calc
      _ = 𝒮[do
        let h ← $ᵗ (Bool × Bool → Bool)
        let sb ← $ᵗ (Bool × Bool)
        pure (h,sb)] := by
          apply evalSPMF_bind_congr_left
          intro h
          have hh := congrArg (Functor.map (f := SPMF) (fun sb : Bool × Bool => (h,sb)))
            (WithdrawGame.ROM.uniform_pair (A := Bool) (B := Bool))
          simpa only [← evalSPMF_map, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using hh
      _ = _ := WithdrawGame.ROM.uniform_pair
  rw [he]
  have hh := congrArg (Functor.map (f := SPMF) win) hd
  simpa only [← evalSPMF_map, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using hh

theorem real_probability : Pr[= true | experiment other adversary] = 5/8 := by
  rw [probOutput_congr (x := true) rfl experiment_eq, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun d : Draw => win d = true)).card = 40 := by decide
  have ht : Fintype.card Draw = 64 := by decide
  simp only [Function.comp_def]
  change _ / _ = _
  rw [hc,ht]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
  norm_num

theorem control_advantage : advantage other adversary = 1/8 := by
  norm_num [advantage, real_probability]

theorem zero_query_bound_false : ¬advantage other adversary ≤ (0 : ℝ) / Fintype.card Bool := by
  rw [control_advantage]
  norm_num

/-- This one-query attacker receives the sampled salt, which the hiding theorem keeps private. -/
def disclosedGuess (salt : Fin 8) (cm : Bool) : OracleComp (attackSpec Bool (Fin 8) Bool Aux) Bool := do
  let a ← liftM ((attackSpec Bool (Fin 8) Bool Aux).query (.inr (.inl (false,salt))))
  pure (!(a == cm))

theorem disclosed_query_bound (salt : Fin 8) (cm : Bool) :
    (disclosedGuess salt cm).IsQueryBoundP (charged (C := Bool) (aux := Aux)) 1 := by
  simp [disclosedGuess, charged]

noncomputable def disclosed : ProbComp Bool := do
  let salt ← $ᵗ (Fin 8)
  let h ← $ᵗ (Bool × Fin 8 → Bool)
  let b ← $ᵗ Bool
  let g ← run other h (disclosedGuess salt (h (b,salt)))
  pure (b == g)

def disclosedWin (d : (Bool → Bool) × Bool) : Bool := d.2 == !(d.1 false == d.1 d.2)

theorem disclosed_probability : Pr[= true | disclosed] = 3/4 := by
  have hp : Pr[= true | do
      let f ← $ᵗ (Bool → Bool); let b ← $ᵗ Bool; pure (disclosedWin (f,b))] = 3/4 := by
    have hh := congrArg (Functor.map (f := SPMF) disclosedWin)
      (WithdrawGame.ROM.uniform_pair (A := Bool → Bool) (B := Bool))
    simp only [← evalSPMF_map, map_bind, map_pure] at hh
    rw [probOutput_congr (x := true) rfl hh, ← probEvent_eq_eq_probOutput,
      probEvent_map, probEvent_uniformSample]
    have hc : (Finset.univ.filter (fun d : (Bool → Bool) × Bool => disclosedWin d = true)).card = 6 := by decide
    have ht : Fintype.card ((Bool → Bool) × Bool) = 8 := by decide
    simp only [Function.comp_def]
    change _ / _ = _
    rw [hc,ht]
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
    norm_num
  unfold disclosed
  rw [probOutput_bind_of_const _ (r := 3/4)]
  · simp
  · intro salt _
    have he := WithdrawGame.ROM.program_bind_restrict (R := Bool) (saltCoord_injective (M := Bool) salt)
      (fun (_h : Bool × Fin 8 → Bool) f => do
        let b ← $ᵗ Bool; pure (disclosedWin (f,b)))
    have hh : Pr[= true | do
        let h ← $ᵗ (Bool × Fin 8 → Bool)
        let b ← $ᵗ Bool
        let g ← run other h (disclosedGuess salt (h (b,salt)))
        pure (b == g)] = Pr[= true | do
          let h ← $ᵗ (Bool × Fin 8 → Bool)
          let b ← $ᵗ Bool
          pure (disclosedWin (h ∘ saltCoord salt,b))] := by
      congr 1
    rw [hh, ← probOutput_congr (x := true) rfl he]
    rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
    exact hp

theorem disclosed_advantage : |(Pr[= true | disclosed]).toReal - 1/2| = 1/4 := by
  norm_num [disclosed_probability]

theorem disclosed_bound_false : ¬|(Pr[= true | disclosed]).toReal - 1/2| ≤
    (1 : ℝ) / Fintype.card (Fin 8) := by
  rw [disclosed_advantage]
  norm_num

end LeanShieldedPool.CommitROM.Control
