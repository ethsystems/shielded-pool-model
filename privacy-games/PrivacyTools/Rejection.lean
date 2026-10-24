import SenderGame.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.PrivacyTools

theorem decide_probability {α : Type} (d : ProbComp α) (p : α → Prop) [DecidablePred p] :
    Pr[= true | do let a ← d; pure (decide (p a))] = Pr[p | d] := by
  simp only [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, probOutput_pure]
  apply tsum_congr
  intro a
  by_cases h : p a <;> simp [h]

theorem partition_four {α : Type} (d : ProbComp α) (bad p q r : α → Prop) :
    (Pr[bad | d]).toReal =
      (Pr[fun a => bad a ∧ p a | d]).toReal +
      (Pr[fun a => bad a ∧ ¬p a ∧ q a | d]).toReal +
      (Pr[fun a => bad a ∧ ¬p a ∧ ¬q a ∧ r a | d]).toReal +
      (Pr[fun a => bad a ∧ ¬p a ∧ ¬q a ∧ ¬r a | d]).toReal := by
  classical
  have he : Pr[bad | d] =
      Pr[fun a => bad a ∧ p a | d] +
      Pr[fun a => bad a ∧ ¬p a ∧ q a | d] +
      Pr[fun a => bad a ∧ ¬p a ∧ ¬q a ∧ r a | d] +
      Pr[fun a => bad a ∧ ¬p a ∧ ¬q a ∧ ¬r a | d] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases hb : bad a <;> by_cases hp : p a <;>
      by_cases hq : q a <;> by_cases hr : r a <;> simp [hb, hp, hq, hr]
  rw [he]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]

end LeanShieldedPool.PrivacyTools

namespace LeanShieldedPool.OwnerGame
open WithdrawGame GameCorrespondence PrivacyTools
variable {P : PrimSpec} {ι : Type}

def PrefixRejected (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = none

def OutputCollision (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι)
    (salt : P.Salt) (b : Bool) : Prop :=
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    (c.deposit keys salt b).note.cm ∈ st.leaves

noncomputable def terms [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ × ℝ × ℝ :=
  let d := draws adv
  let bad := fun a => ¬ Legal sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2
  let pref := fun a => PrefixRejected sup a.1 a.2.1
  let col := fun a => OutputCollision sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2
  ((Pr[fun a => bad a ∧ pref a | d]).toReal,
   (Pr[fun a => bad a ∧ ¬pref a ∧ col a | d]).toReal,
   (Pr[fun a => bad a ∧ ¬pref a ∧ ¬col a | d]).toReal)

theorem rejection_partition [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    rejectionProbability sup adv = (terms sup adv).1 + (terms sup adv).2.1 + (terms sup adv).2.2 := by
  classical
  unfold rejectionProbability
  rw [decide_probability]
  have h := partition_four (draws adv)
    (fun a => ¬ Legal sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2)
    (fun a => PrefixRejected sup a.1 a.2.1)
    (fun a => OutputCollision sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2) (fun _ => False)
  simpa [terms] using h

theorem advantage_le_explicit [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) (ε : ℝ) (hHide : Hiding (P := P) ε) :
    advantage sup adv ≤ ε / 2 +
      ((terms sup adv).1 + (terms sup adv).2.1 + (terms sup adv).2.2) / 2 := by
  simpa only [rejection_partition] using advantage_le sup adv ε hHide

end LeanShieldedPool.OwnerGame

namespace LeanShieldedPool.SenderGame
open WithdrawGame GameCorrespondence PrivacyTools
variable {P : PrimSpec} {ι : Type}

def PrefixRejected (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = none

def InputCollision (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι)
    (s₁ s₂ : P.Salt) : Prop :=
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    ∃ b, let tx := (c.world b).transfer keys s₁ s₂ c.snapshot
         tx.nf1 ∈ st.nullifiers ∨ tx.nf2 ∈ st.nullifiers ∨ tx.nf1 = tx.nf2

def OutputCollision (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι)
    (s₁ s₂ : P.Salt) : Prop :=
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    ∃ b, let tx := (c.world b).transfer keys s₁ s₂ c.snapshot
         tx.out1.cm ∈ st.leaves ∨ tx.out2.cm ∈ st.leaves ∨ tx.out1.cm = tx.out2.cm

/-- Priority partition: failed prefix, input collisions, output collisions, other illegality.
The output term excludes samples already charged to an input collision. -/
noncomputable def terms [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ × ℝ × ℝ × ℝ :=
  let d := draws adv
  let bad := fun a => ¬ Legal sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1
  let pref := fun a => PrefixRejected sup a.1 a.2.1
  let inp := fun a => InputCollision sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1
  let out := fun a => OutputCollision sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1
  ((Pr[fun a => bad a ∧ pref a | d]).toReal,
   (Pr[fun a => bad a ∧ ¬pref a ∧ inp a | d]).toReal,
   (Pr[fun a => bad a ∧ ¬pref a ∧ ¬inp a ∧ out a | d]).toReal,
   (Pr[fun a => bad a ∧ ¬pref a ∧ ¬inp a ∧ ¬out a | d]).toReal)

theorem rejection_partition [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    rejectionProbability sup adv = (terms sup adv).1 + (terms sup adv).2.1 +
      (terms sup adv).2.2.1 + (terms sup adv).2.2.2 := by
  classical
  unfold rejectionProbability
  rw [decide_probability]
  exact partition_four (draws adv) _ _ _ _

theorem advantage_le_explicit [Fintype ι] [Finite P.Commitment]
    [Finite P.Nullifier] [Nonempty P.Nullifier] [SampleableType P.Nullifier]
    [SampleableType P.Salt] [SampleableType (ι → P.SpendKey)] [SampleableType (WithdrawGame.Transport.Table P ι)]
    (sup : P.Token → Prop) (adv : Adversary P ι) (εPRF εHide : ℝ)
    (hPRF : WithdrawGame.Transport.MultiKeyPublicKeyPRF (P := P) (ι := ι) (Fintype.card ι * εPRF))
    (hε : 0 ≤ εHide) (hHide : OwnerGame.Hiding (P := P) εHide) :
    advantage sup adv ≤ Fintype.card ι * εPRF + εHide +
      ((terms sup adv).1 + (terms sup adv).2.1 + (terms sup adv).2.2.1 + (terms sup adv).2.2.2) / 2 := by
  simpa only [rejection_partition] using advantage_le sup adv _ εHide hPRF hε hHide

end LeanShieldedPool.SenderGame
