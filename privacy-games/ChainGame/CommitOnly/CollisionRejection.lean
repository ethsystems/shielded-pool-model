import CommitROM.TableCollision
import ChainGame.CommitOnly.Security

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [SampleableType (Model.Table P cap)]

def TableValid (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t : Nat) (hc : Model.Table P cap) : Prop :=
  ∃ st : St (commitPrim P cap hc),
    Run (P := commitPrim P cap hc) sup
      (setup.map (RecipientGame.ROMCommit.rebaseTx P.derivePub (fun x => P.nullify x.2 x.1) hc)) st ∧
    st.minted.length ≤ m ∧
    ∀ x ∈ support (run (WithdrawGame.ROM.answers P.derivePub (fun x => P.nullify x.2 x.1)) hc adv.choose),
      ChainGame.WellFormed t st [] (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.1.val) ∧
      ChainGame.WellFormed t st [] (worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc x.2.1.val)

noncomputable def validityFailureProbability (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t : Nat) : ℝ :=
  (Pr[fun hc : Model.Table P cap => Function.Injective hc ∧ ¬TableValid sup setup adv m t hc |
    $ᵗ (Model.Table P cap)]).toReal

theorem at_rejection_le (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t qC qN : Nat) (hc : Model.Table P cap)
    (hv : TableValid sup setup adv m t hc)
    (sc : RecipientGame.Rejection.CommitmentSpread (P := commitPrim P cap hc) qC)
    (sn : ChainGame.NullifierSpread (P := commitPrim P cap hc) qN) :
    Pr[fun d => rejected sup adv P.derivePub (fun x => P.nullify x.2 x.1) hc d = true |
      atDraws setup adv P.derivePub (fun x => P.nullify x.2 x.1) hc] ≤
      ChainGame.exposureBound m n t qC qN := by
  classical
  obtain ⟨st,hrun,hm,hw⟩ := hv
  unfold atDraws
  apply probEvent_bind_le_of_forall_le
  intro x hx
  rcases x with ⟨l,r,s⟩
  dsimp only
  split
  · apply probEvent_bind_le_of_forall_le
    intro b _
    have hwb : ChainGame.WellFormed t st []
        (if b then worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc r.val
          else worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc l.val) := by
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact (hw (l,r,s) hx).1
      · exact (hw (l,r,s) hx).2
    have hlb : (if b then worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc r.val
          else worldBack P.derivePub (fun x => P.nullify x.2 x.1) hc l.val).length ≤ n := by
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte,worldBack,List.length_map]
      · exact l.property
      · exact r.property
    have h := ChainGame.sampleWorld_rejection_le qC qN t sc sn st [] _ hwb
    have hb := ChainGame.exposureBound_mono hm hlb t qC qN
    have hr := RecipientGame.runChecked_complete hrun
    simpa [probEvent_bind_pure_comp,Function.comp_def,rejected,RecipientGame.runChecked_append,hr]
      using h.trans hb
  · simp [rejected]

variable [Fintype P.Salt]

theorem oracle_salt_injective (hc : Model.Table P cap) (hi : Function.Injective hc)
    (outside : ∀ token amount owner, cap ≤ amount → Function.Injective (P.commit token amount owner)) :
    RecipientGame.Rejection.SaltInjective (commitPrim P cap hc) := by
  constructor
  intro token amount owner a b he
  by_cases h : amount < cap
  · simp only [commitPrim,oraclePrim,h,↓reduceDIte] at he
    exact congrArg Prod.snd (hi he)
  · simp only [commitPrim,oraclePrim,h,↓reduceDIte] at he
    exact outside token amount owner (Nat.le_of_not_gt h) he

theorem rejection_le_validity_add_table_collision (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t : Nat)
    (outside : ∀ token amount owner, cap ≤ amount → Function.Injective (P.commit token amount owner))
    (nullify : ∀ key, Function.Injective (fun cm => P.nullify cm key)) :
    rejectionProbability sup setup adv ≤ validityFailureProbability sup setup adv m t +
      (Pr[fun hc : Model.Table P cap => ¬Function.Injective hc | $ᵗ (Model.Table P cap)]).toReal +
      ChainGame.delta m n t (Fintype.card P.Salt) (Fintype.card P.Salt) := by
  classical
  let bad := fun hc : Model.Table P cap =>
    (Function.Injective hc ∧ ¬TableValid sup setup adv m t hc) ∨ ¬Function.Injective hc
  have hb : Pr[fun b : Bool => b = true | do
      let hc ← $ᵗ (Model.Table P cap)
      let d ← atDraws setup adv P.derivePub (fun x => P.nullify x.2 x.1) hc
      pure (rejected sup adv P.derivePub (fun x => P.nullify x.2 x.1) hc d)] ≤
      Pr[bad | $ᵗ (Model.Table P cap)] +
        ChainGame.exposureBound m n t (Fintype.card P.Salt) (Fintype.card P.Salt) := by
    apply probEvent_bind_le_probEvent_add
    intro hc _ hn
    have hi : Function.Injective hc := by tauto
    have hv : TableValid sup setup adv m t hc := by tauto
    have sc := RecipientGame.Rejection.spread_of_injective (oracle_salt_injective hc hi outside)
    have sn := ChainGame.nullifierSpread_of_injective _ sc nullify
    rw [bind_pure_comp,probEvent_map]
    exact at_rejection_le sup setup adv m t _ _ hc hv sc sn
  have hb' := hb.trans (add_le_add (probEvent_or_le _ _ _) le_rfl)
  have hs : (Fintype.card P.Salt : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr := ENNReal.toReal_mono (by unfold ChainGame.exposureBound; finiteness) hb'
  rw [ENNReal.toReal_add (by finiteness) (by unfold ChainGame.exposureBound; finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  have he : (ChainGame.exposureBound m n t (Fintype.card P.Salt) (Fintype.card P.Salt)).toReal =
      ChainGame.delta m n t (Fintype.card P.Salt) (Fintype.card P.Salt) := by
    unfold ChainGame.exposureBound
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
      RecipientGame.Rejection.exposures_closed,ChainGame.delta,div_eq_mul_inv]
  rw [he] at hr
  simpa only [rejectionProbability,validityFailureProbability,probEvent_eq_eq_probOutput] using hr

variable [Fintype P.Token] [Fintype P.PubKey] [Fintype P.Commitment]
  [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Message P cap → P.Commitment)]

theorem full_table_collision_le :
    (Pr[fun hc : Model.Table P cap => ¬Function.Injective hc | $ᵗ (Model.Table P cap)]).toReal ≤
      (Fintype.card (Message P cap × P.Salt) : ℝ) * (Fintype.card (Message P cap × P.Salt)-1) /
        (2*Fintype.card P.Commitment) := by
  classical
  have h := table_collision_le_real (C := P.Commitment)
    (Finset.univ : Finset (Message P cap × P.Salt)).toList (Finset.nodup_toList _)
  have he (hc : Model.Table P cap) :
      ((Finset.univ : Finset (Message P cap × P.Salt)).toList.map hc).Nodup ↔ Function.Injective hc := by
    constructor
    · intro h a b hab
      exact List.inj_on_of_nodup_map h (by simp) (by simp) hab
    · intro h
      exact List.Nodup.map h (Finset.nodup_toList _)
  simpa only [he,Finset.length_toList,Finset.card_univ] using h

theorem rejection_le_rom_collisions (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t : Nat)
    (outside : ∀ token amount owner, cap ≤ amount → Function.Injective (P.commit token amount owner))
    (nullify : ∀ key, Function.Injective (fun cm => P.nullify cm key)) :
    rejectionProbability sup setup adv ≤ validityFailureProbability sup setup adv m t +
      (Fintype.card (Message P cap × P.Salt) : ℝ) * (Fintype.card (Message P cap × P.Salt)-1) /
        (2*Fintype.card P.Commitment) +
      ChainGame.delta m n t (Fintype.card P.Salt) (Fintype.card P.Salt) := by
  have h := rejection_le_validity_add_table_collision sup setup adv m t outside nullify
  have hc := full_table_collision_le (P := P) (cap := cap)
  linarith

theorem advantage_le_rom_collisions (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P cap n) (m t qc qg : Nat) (hq : QueryBound adv qc qg)
    (outside : ∀ token amount owner, cap ≤ amount → Function.Injective (P.commit token amount owner))
    (nullify : ∀ key, Function.Injective (fun cm => P.nullify cm key)) :
    advantage sup setup adv ≤
      (2*n : ℝ)*(qc+qg+4*setup.length+6*n)/Fintype.card P.Salt +
      (validityFailureProbability sup setup adv m t +
        (Fintype.card (Message P cap × P.Salt) : ℝ)*(Fintype.card (Message P cap × P.Salt)-1)/
          (2*Fintype.card P.Commitment) +
        ChainGame.delta m n t (Fintype.card P.Salt) (Fintype.card P.Salt))/2 := by
  have h := advantage_le_queryBound sup setup adv qc qg hq
  have hr := rejection_le_rom_collisions sup setup adv m t outside nullify
  linarith

end LeanShieldedPool.ChainGame.CommitOnly
