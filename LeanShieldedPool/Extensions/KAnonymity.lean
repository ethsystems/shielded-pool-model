import LeanShieldedPool.Pool.Events
import LeanShieldedPool.Statements.L3
import Mathlib.Logic.Equiv.Fintype

/-!
# Symbolic observation and anonymity sets

The observer sees the ordered `Event` log. Commitment and nullifier atoms
have separate equality patterns. Renaming preserves constructors and slots,
including repeated atoms across different events. There is no relation
between the two renamings, even if their carrier types happen to coincide.

JUSTIFICATION: `HashHidingHyp` is a named hiding assumption, not a theorem
about the observer's real power. It assumes hashes hide their inputs and
nullifiers cannot be linked to commitments without spending keys (spec
line 424). `CryptoHyp` supplies collision freedom, not this hiding property.
Any real privacy claim must state this assumption explicitly. This file proves only properties of the symbolic relation.
The observer omits keys, encrypted payloads, and other on-chain or network
data outside `Event`; it does not model the full public observer by itself.
-/

namespace LeanShieldedPool.KAnonymity

variable {P : PrimSpec}

/-- Rename atoms without changing event constructors or slot order. -/
def renameEvent (cm : P.Commitment → P.Commitment)
    (nf : P.Nullifier → P.Nullifier) : Event P → Event P
  | .deposit c => .deposit (cm c)
  | .transfer n₁ n₂ c₁ c₂ => .transfer (nf n₁) (nf n₂) (cm c₁) (cm c₂)
  | .withdraw n => .withdraw (nf n)

/-- Global injections preserve and reflect each sort's equality pattern. -/
def ObsEquiv (log₁ log₂ : List (Event P)) : Prop :=
  ∃ (cm : P.Commitment ↪ P.Commitment) (nf : P.Nullifier ↪ P.Nullifier),
    log₁.map (renameEvent cm nf) = log₂

private def commitmentAtoms : Event P → List P.Commitment
  | .deposit c => [c]
  | .transfer _ _ c₁ c₂ => [c₁, c₂]
  | .withdraw _ => []

private def nullifierAtoms : Event P → List P.Nullifier
  | .deposit _ => []
  | .transfer n₁ n₂ _ _ => [n₁, n₂]
  | .withdraw n => [n]

/-- Only finitely many atoms occur. Extend their injection to a permutation;
an arbitrary global injection need not itself have an inverse. -/
private theorem extendOnList {α : Type} (f : α ↪ α) (xs : List α) :
    ∃ p : Equiv.Perm α, ∀ x ∈ xs, p x = f x := by
  classical
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun x : xs.toFinset => (x : α)) (fun x : xs.toFinset => f x)
    Subtype.val_injective (f.injective.comp Subtype.val_injective)
  refine ⟨p, ?_⟩
  intro x hx
  exact hp ⟨x, List.mem_toFinset.mpr hx⟩

private theorem renameEvent_congr
    (cm cm' : P.Commitment → P.Commitment) (nf nf' : P.Nullifier → P.Nullifier)
    (e : Event P)
    (hc : ∀ c ∈ commitmentAtoms e, cm c = cm' c)
    (hn : ∀ n ∈ nullifierAtoms e, nf n = nf' n) :
    renameEvent cm nf e = renameEvent cm' nf' e := by
  cases e with
  | deposit c =>
    exact congrArg Event.deposit (hc c List.mem_cons_self)
  | transfer n₁ n₂ c₁ c₂ =>
    change Event.transfer _ _ _ _ = Event.transfer _ _ _ _
    congr 1
    · exact hn n₁ List.mem_cons_self
    · exact hn n₂ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact hc c₁ List.mem_cons_self
    · exact hc c₂ (List.mem_cons_of_mem _ List.mem_cons_self)
  | withdraw n =>
    exact congrArg Event.withdraw (hn n List.mem_cons_self)

/-- Permutations give exactly the same finite-log relation as injections. -/
theorem obsEquiv_iff_permutations (log₁ log₂ : List (Event P)) :
    ObsEquiv log₁ log₂ ↔
      ∃ (cm : Equiv.Perm P.Commitment) (nf : Equiv.Perm P.Nullifier),
        log₁.map (renameEvent cm nf) = log₂ := by
  constructor
  · rintro ⟨cm, nf, h⟩
    obtain ⟨pc, hc⟩ := extendOnList cm (log₁.flatMap commitmentAtoms)
    obtain ⟨pn, hn⟩ := extendOnList nf (log₁.flatMap nullifierAtoms)
    refine ⟨pc, pn, Eq.trans ?_ h⟩
    apply List.map_congr_left
    intro e he
    apply renameEvent_congr
    · intro c hmem
      exact hc c (List.mem_flatMap.mpr ⟨e, he, hmem⟩)
    · intro n hmem
      exact hn n (List.mem_flatMap.mpr ⟨e, he, hmem⟩)
  · rintro ⟨cm, nf, h⟩
    exact ⟨cm.toEmbedding, nf.toEmbedding, h⟩

theorem ObsEquiv.refl (log : List (Event P)) : ObsEquiv log log := by
  refine ⟨Function.Embedding.refl _, Function.Embedding.refl _, ?_⟩
  have h : renameEvent (P := P) id id = id := by
    funext e
    cases e <;> rfl
  change log.map (renameEvent id id) = log
  rw [h, List.map_id]

theorem ObsEquiv.symm {log₁ log₂ : List (Event P)}
    (h : ObsEquiv log₁ log₂) : ObsEquiv log₂ log₁ := by
  obtain ⟨cm, nf, hmap⟩ := (obsEquiv_iff_permutations _ _).mp h
  apply (obsEquiv_iff_permutations _ _).mpr
  refine ⟨cm.symm, nf.symm, ?_⟩
  rw [← hmap, List.map_map]
  have hinv : (renameEvent (P := P) cm.symm nf.symm ∘ renameEvent cm nf) = id := by
    funext e
    cases e <;> simp only [Function.comp_apply, renameEvent, Equiv.symm_apply_apply,
      id_eq]
  rw [hinv, List.map_id]

theorem ObsEquiv.trans {log₁ log₂ log₃ : List (Event P)}
    (h₁₂ : ObsEquiv log₁ log₂) (h₂₃ : ObsEquiv log₂ log₃) :
    ObsEquiv log₁ log₃ := by
  obtain ⟨cm₁, nf₁, h₁⟩ := h₁₂
  obtain ⟨cm₂, nf₂, h₂⟩ := h₂₃
  refine ⟨cm₁.trans cm₂, nf₁.trans nf₂, ?_⟩
  rw [← h₂, ← h₁, List.map_map]
  apply List.map_congr_left
  intro e _
  cases e <;> rfl

theorem obsEquiv_equivalence : Equivalence (ObsEquiv (P := P)) :=
  ⟨ObsEquiv.refl, ObsEquiv.symm, ObsEquiv.trans⟩

/-- The constructor at each log position remains observable. -/
def eventShape : Event P → Fin 3
  | .deposit _ => 0
  | .transfer _ _ _ _ => 1
  | .withdraw _ => 2

theorem ObsEquiv.shapes {log₁ log₂ : List (Event P)}
    (h : ObsEquiv log₁ log₂) : log₁.map eventShape = log₂.map eventShape := by
  obtain ⟨cm, nf, hmap⟩ := h
  rw [← hmap, List.map_map]
  apply List.map_congr_left
  intro e _
  cases e <;> rfl

theorem not_obsEquiv_of_shapes_ne {log₁ log₂ : List (Event P)}
    (h : log₁.map eventShape ≠ log₂.map eventShape) : ¬ ObsEquiv log₁ log₂ :=
  fun he => h he.shapes

/-- Different commitment values alone do not distinguish singleton deposits. -/
theorem deposit_obsEquiv (c d : P.Commitment) :
    ObsEquiv [Event.deposit c] [Event.deposit d] := by
  classical
  apply (obsEquiv_iff_permutations _ _).mpr
  refine ⟨Equiv.swap c d, Equiv.refl _, ?_⟩
  simp only [List.map_cons, List.map_nil, renameEvent, Equiv.swap_apply_left]

/-- Same length, different constructors: these logs are distinguishable. -/
theorem deposit_not_obsEquiv_withdraw (c : P.Commitment) (n : P.Nullifier) :
    ¬ ObsEquiv [Event.deposit c] [Event.withdraw n] := by
  apply not_obsEquiv_of_shapes_ne
  intro h
  have hzero : (0 : Fin 3) = 2 := (List.cons.inj h).1
  have hnat : (0 : Nat) = 2 := congrArg Fin.val hzero
  cases hnat

/-- Equal slots cannot be renamed to unequal slots, even across events. -/
theorem repeated_deposit_not_obsEquiv (a b c : P.Commitment) (hbc : b ≠ c) :
    ¬ ObsEquiv [Event.deposit a, Event.deposit a]
      [Event.deposit b, Event.deposit c] := by
  rintro ⟨cm, nf, h⟩
  have hb : cm a = b := Event.deposit.inj (List.cons.inj h).1
  have hc : cm a = c := Event.deposit.inj (List.cons.inj (List.cons.inj h).2).1
  exact hbc (hb.symm.trans hc)

/-- Injectivity also prevents distinct atoms from collapsing to one atom. -/
theorem distinct_deposits_not_obsEquiv (a b c : P.Commitment) (hab : a ≠ b) :
    ¬ ObsEquiv [Event.deposit a, Event.deposit b]
      [Event.deposit c, Event.deposit c] :=
  fun h => repeated_deposit_not_obsEquiv c a b hab h.symm

/-- Named external assumption: the chosen real observer cannot distinguish
symbolically equivalent logs. Instantiating `CannotDistinguish` and justifying
this implication require a hiding model; no such result is proved here. -/
def HashHidingHyp (CannotDistinguish : List (Event P) → List (Event P) → Prop) : Prop :=
  ∀ log₁ log₂, ObsEquiv log₁ log₂ → CannotDistinguish log₁ log₂

/-- Accepted histories and final states compatible with this symbolic log.
The supported-token set is fixed across all explanations. Cryptographic
collision freedom is required separately within each history. -/
def explanations (sup : P.Token → Prop) (log : List (Event P)) :
    Set (List (Tx P) × St P) :=
  {e | Run sup e.1 e.2 ∧ CryptoHyp P e.1 ∧ ObsEquiv (events e.1) log}

/-- Find the last transfer, allowing deposits or withdrawals after it. -/
def lastTransfer : List (Tx P) → Option (TransferData P)
  | [] => none
  | tx :: txs =>
    match lastTransfer txs with
    | some d => some d
    | none =>
      match tx with
      | .transfer d => some d
      | _ => none

/-- Absence is explicit, so a missing transfer cannot supply a recipient. -/
def lastTransferFirstOwner (txs : List (Tx P)) : Option P.PubKey :=
  (lastTransfer txs).map (fun d => d.out1.ownerPubkey)

example (d e : TransferData P) (dep : DepositData P) (w : WithdrawData P) :
    lastTransferFirstOwner [.transfer d, .transfer e, .deposit dep, .withdraw w] =
      some e.out1.ownerPubkey := rfl

example (dep : DepositData P) (w : WithdrawData P) :
    lastTransferFirstOwner [.deposit dep, .withdraw w] = none := rfl

/-- At least `k` distinct explanations, with pairwise distinct owners of the
first output of their last transfer. Each chosen history must contain a
transfer, including when `k = 1`. The case `k = 0` is vacuous by design.
This counts possible owners; it assigns no probabilities or equal likelihood. -/
def hasAnonymitySet (sup : P.Token → Prop) (log : List (Event P)) (k : Nat) : Prop :=
  ∃ (es : Fin k → List (Tx P) × St P) (owners : Fin k → P.PubKey),
    (∀ i, es i ∈ explanations sup log) ∧
    Function.Injective es ∧ Function.Injective owners ∧
    ∀ i, lastTransferFirstOwner (es i).1 = some (owners i)

/-- Restrict an anonymity family to any smaller count. -/
theorem hasAnonymitySet.mono {sup : P.Token → Prop} {log : List (Event P)}
    {m k : Nat} (h : hasAnonymitySet sup log k) (hm : m ≤ k) :
    hasAnonymitySet sup log m := by
  obtain ⟨es, owners, he, hi, ho, hr⟩ := h
  let f : Fin m ↪ Fin k := ⟨fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩,
    fun _ _ h => Fin.ext (congrArg (Fin.val (n := k)) h)⟩
  exact ⟨es ∘ f, owners ∘ f, fun i => he (f i), hi.comp f.injective,
    ho.comp f.injective, fun i => hr (f i)⟩

/-- Zero requires no explanations, even for a log with no accepted history. -/
theorem hasAnonymitySet_zero (sup : P.Token → Prop) (log : List (Event P)) :
    hasAnonymitySet sup log 0 := by
  refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

private theorem lastTransfer_mem {txs : List (Tx P)} {d : TransferData P}
    (h : lastTransfer txs = some d) : Tx.transfer d ∈ txs := by
  induction txs with
  | nil => cases h
  | cons tx txs ih =>
    cases ht : lastTransfer txs with
    | some e =>
      simp only [lastTransfer, ht] at h
      have he : e = d := Option.some.inj h
      exact List.mem_cons_of_mem _ (ih (ht.trans (congrArg some he)))
    | none =>
      cases tx with
      | deposit dep =>
        simp only [lastTransfer, ht] at h
        cases h
      | withdraw w =>
        simp only [lastTransfer, ht] at h
        cases h
      | transfer e =>
        simp only [lastTransfer, ht] at h
        have he : e = d := Option.some.inj h
        subst e
        exact List.mem_cons_self

private theorem run_transfer_guard {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (hr : Run sup txs st)
    {d : TransferData P} (hd : Tx.transfer d ∈ txs) :
    ∃ before : St P, d.guard before := by
  induction hr with
  | empty => cases hd
  | step hr hs ih =>
    rcases List.mem_append.mp hd with hd | hd
    · exact ih hd
    · have he := List.mem_singleton.mp hd
      subst he
      cases hs with
      | transfer hg => exact ⟨_, hg⟩

/-- A positive count supplies a transfer from an accepted explanation. -/
theorem hasAnonymitySet.accepted_transfer {sup : P.Token → Prop}
    {log : List (Event P)} {k : Nat} (h : hasAnonymitySet sup log k)
    (hk : 0 < k) : ∃ (d : TransferData P) (st : St P), d.guard st := by
  obtain ⟨es, owners, he, _, _, hr⟩ := h
  let i : Fin k := ⟨0, hk⟩
  have howner := hr i
  cases ht : lastTransfer (es i).1 with
  | none =>
    simp only [lastTransferFirstOwner, ht, Option.map_none] at howner
    cases howner
  | some d => exact ⟨d, run_transfer_guard (he i).1 (lastTransfer_mem ht)⟩

end LeanShieldedPool.KAnonymity

namespace LeanShieldedPool.KAnonymity

/-- Candidate conclusion for a chosen primitive profile and supported tokens.
Key and salt cardinalities alone do not imply this proposition. -/
def acceptedAnonymityCandidate (P : PrimSpec) (sup : P.Token → Prop) (k : Nat) : Prop :=
  ∃ (txs : List (Tx P)) (st : St P),
    Run sup txs st ∧ CryptoHyp P txs ∧ hasAnonymitySet sup (events txs) k

theorem acceptedAnonymityCandidate.mono {sup : P.Token → Prop} {m k : Nat}
    (h : acceptedAnonymityCandidate P sup k) (hm : m ≤ k) :
    acceptedAnonymityCandidate P sup m := by
  obtain ⟨txs, st, hr, hc, ha⟩ := h
  exact ⟨txs, st, hr, hc, ha.mono hm⟩

/-- The proposed cardinality-only implication, stated but not asserted.
Even infinitely many salts cannot force a constant commitment function to
produce the distinct output atoms required by an accepted transfer. -/
def cardinalityOnlyCandidate (P : PrimSpec) (sup : P.Token → Prop) (k : Nat) : Prop :=
  Nonempty (Fin k ↪ P.PubKey) → Nonempty (Nat ↪ P.Salt) →
    acceptedAnonymityCandidate P sup k

/-- A concrete obstruction to the cardinality-only proposal. -/
theorem constant_commit_blocks_transfer {P : PrimSpec} (c : P.Commitment)
    (hc : ∀ token amount owner salt, P.commit token amount owner salt = c)
    (d : TransferData P) (st : St P) : ¬ d.guard st := by
  intro hg
  simp only [TransferData.guard, Note.cm, hc, ne_eq, not_true_eq_false,
    and_false] at hg

theorem constant_commit_not_candidate {sup : P.Token → Prop} {k : Nat}
    (c : P.Commitment)
    (hc : ∀ token amount owner salt, P.commit token amount owner salt = c)
    (hk : 0 < k) : ¬ acceptedAnonymityCandidate P sup k := by
  rintro ⟨_, _, _, _, ha⟩
  obtain ⟨d, st, hg⟩ := ha.accepted_transfer hk
  exact constant_commit_blocks_transfer c hc d st hg

namespace ConstantCommitToy

/-- Infinitely many keys and salts cannot repair a constant commitment. -/
abbrev Toy : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Nat
  SpendKey := Nat
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat
  derivePub := id
  commit := fun _ _ _ _ => 0
  nullify := fun cm _ => cm

abbrev sup : Toy.Token → Prop := fun _ => True

theorem enough_pubkeys (k : Nat) : Nonempty (Fin k ↪ Toy.PubKey) :=
  ⟨⟨Fin.val, Fin.val_injective⟩⟩

theorem infinite_salts : Nonempty (Nat ↪ Toy.Salt) :=
  ⟨Function.Embedding.refl _⟩

/-- The full cardinality implication is false for every positive count. -/
theorem not_cardinalityOnlyCandidate (k : Nat) (hk : 0 < k) :
    ¬ cardinalityOnlyCandidate Toy sup k := by
  intro h
  exact constant_commit_not_candidate (P := Toy) 0 (fun _ _ _ _ => rfl) hk
    (h (enough_pubkeys k) infinite_salts)

end ConstantCommitToy

namespace TwoRecipientToy

/-- Salt atoms witness the symbolic relation only. These functions are not
cryptographic hashes; collision freedom will be checked within each run. -/
abbrev Toy : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Fin 2
  SpendKey := Fin 2
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat
  derivePub := id
  commit := fun _ _ _ salt => salt
  nullify := fun cm _ => cm

abbrev sup : Toy.Token → Prop := fun _ => True
abbrev input : Note Toy := ⟨(), 5, 0, 0⟩
abbrev ballast : Note Toy := ⟨(), 0, 0, 1⟩
abbrev deposit : DepositData Toy := ⟨input, ()⟩

/-- Both worlds spend the same deposit. Only output owners and salts vary. -/
abbrev transfer (i : Fin 2) : TransferData Toy :=
  { key := 0
    in1 := input
    in2 := ballast
    out1 := ⟨(), 3, i, 2 + 2 * i.val⟩
    out2 := ⟨(), 2, 0, 3 + 2 * i.val⟩
    snapshot := 1 }

def history (i : Fin 2) : List (Tx Toy) := [.deposit deposit, .transfer (transfer i)]

noncomputable def finalState (i : Fin 2) : St Toy :=
  (transfer i).post (deposit.post (St.empty Toy sup))

theorem deposit_guard : deposit.guard (St.empty Toy sup) := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.cm, U128, maxU128]

theorem transfer_guard (i : Fin 2) :
    (transfer i).guard (deposit.post (St.empty Toy sup)) := by
  fin_cases i <;>
    norm_num [TransferData.guard, TransferData.nf1, TransferData.nf2, Note.nf,
      Note.cm, Note.ownedBy, Note.isBallast, St.rootInWindow, St.inTreeAt,
      St.fresh, St.leaves, St.empty, St.pushWindow, rootWindow, DepositData.post,
      U128, maxU128]

theorem accepted (i : Fin 2) : Run sup (history i) (finalState i) := by
  exact Run.step (Run.step Run.empty (Step.deposit deposit_guard))
    (Step.transfer (transfer_guard i))

theorem crypto (i : Fin 2) : CryptoHyp Toy (history i) := by
  constructor
  · intro n hn n' hn' _ _ h
    simp only [history, runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | (fin_cases i <;> norm_num [Note.cm] at h)
  · intro key _ key' _ h
    exact h

/-- Collision freedom also holds across both worlds' combined witnesses.
The concatenation is a witness collection, not an asserted accepted run. -/
theorem crypto_cross_history : CryptoHyp Toy (history 0 ++ history 1) := by
  constructor
  · intro n hn n' hn' _ _ h
    simp only [history, runNotes, List.flatMap_cons,
      List.flatMap_nil, Tx.notes, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | norm_num [Note.cm] at h
  · intro key _ key' _ h
    exact h

theorem recipient (i : Fin 2) : lastTransferFirstOwner (history i) = some i := rfl

private theorem zero_obs_one : ObsEquiv (events (history 0)) (events (history 1)) := by
  apply (obsEquiv_iff_permutations _ _).mpr
  refine ⟨(Equiv.swap 2 4).trans (Equiv.swap 3 5), Equiv.refl _, ?_⟩
  norm_num [history, events, Tx.event, Note.cm, TransferData.nf1,
    TransferData.nf2, Note.nf, renameEvent, Equiv.swap_apply_def]

/-- Every pair of accepted worlds has the same symbolic observation. -/
theorem pairwise_obs (i j : Fin 2) : ObsEquiv (events (history i)) (events (history j)) := by
  fin_cases i <;> fin_cases j
  · exact ObsEquiv.refl _
  · exact zero_obs_one
  · exact zero_obs_one.symm
  · exact ObsEquiv.refl _

theorem anonymity_two : hasAnonymitySet sup (events (history 0)) 2 := by
  refine ⟨fun i => (history i, finalState i), id, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨accepted i, crypto i, pairwise_obs i 0⟩
  · intro i j h
    have hr := congrArg (fun e : List (Tx Toy) × St Toy =>
      lastTransferFirstOwner e.1) h
    exact Option.some.inj hr
  · exact Function.injective_id
  · exact recipient

/-- A concrete accepted history with two distinct accepted recipient assignments. -/
theorem candidate_two : acceptedAnonymityCandidate Toy sup 2 :=
  ⟨history 0, finalState 0, accepted 0, crypto 0, anonymity_two⟩

/-- The connection to a chosen observer is conditional on the named abstraction. -/
theorem indistinguishable_under_hiding
    (CannotDistinguish : List (Event Toy) → List (Event Toy) → Prop)
    (hhide : HashHidingHyp CannotDistinguish) (i j : Fin 2) :
    CannotDistinguish (events (history i)) (events (history j)) :=
  hhide _ _ (pairwise_obs i j)

end TwoRecipientToy

namespace ManyRecipientToy

/-- Owner-independent commitments give equal logs with fixed output salts.
Collision freedom is scoped to each history, not their combined witnesses. -/
abbrev Toy' (k : Nat) : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Fin k
  SpendKey := Fin k
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat
  derivePub := id
  commit := fun _ _ _ salt => salt
  nullify := fun cm _ => cm

variable {k : Nat}

abbrev sup : (Toy' k).Token → Prop := fun _ => True
abbrev baseOwner (hk : 0 < k) : Fin k := ⟨0, hk⟩
abbrev input (hk : 0 < k) : Note (Toy' k) := ⟨(), 5, baseOwner hk, 0⟩
abbrev ballast (hk : 0 < k) : Note (Toy' k) := ⟨(), 0, baseOwner hk, 1⟩
abbrev deposit (hk : 0 < k) : DepositData (Toy' k) := ⟨input hk, ()⟩

/-- Only the first output owner varies with the world index. -/
abbrev transfer (hk : 0 < k) (i : Fin k) : TransferData (Toy' k) :=
  { key := baseOwner hk
    in1 := input hk
    in2 := ballast hk
    out1 := ⟨(), 3, i, 2⟩
    out2 := ⟨(), 2, baseOwner hk, 3⟩
    snapshot := 1 }

def history (hk : 0 < k) (i : Fin k) : List (Tx (Toy' k)) :=
  [.deposit (deposit hk), .transfer (transfer hk i)]

noncomputable def finalState (hk : 0 < k) (i : Fin k) : St (Toy' k) :=
  (transfer hk i).post ((deposit hk).post (St.empty (Toy' k) sup))

theorem deposit_guard (hk : 0 < k) :
    (deposit hk).guard (St.empty (Toy' k) sup) := by
  norm_num [DepositData.guard, St.empty, St.leaves, Note.cm, U128, maxU128]

theorem transfer_guard (hk : 0 < k) (i : Fin k) :
    (transfer hk i).guard ((deposit hk).post (St.empty (Toy' k) sup)) := by
  norm_num [TransferData.guard, TransferData.nf1, TransferData.nf2, Note.nf,
    Note.cm, Note.ownedBy, Note.isBallast, St.rootInWindow, St.inTreeAt,
    St.fresh, St.leaves, St.empty, St.pushWindow, rootWindow, DepositData.post,
    U128, maxU128]

theorem accepted (hk : 0 < k) (i : Fin k) :
    Run sup (history hk i) (finalState hk i) :=
  Run.step (Run.step Run.empty (Step.deposit (deposit_guard hk)))
    (Step.transfer (transfer_guard hk i))

theorem crypto (hk : 0 < k) (i : Fin k) : CryptoHyp (Toy' k) (history hk i) := by
  constructor
  · intro n hn n' hn' _ _ h
    simp only [history, runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hn hn'
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hn' with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | norm_num [Note.cm] at h
  · intro key _ key' _ h
    exact h

theorem recipient (hk : 0 < k) (i : Fin k) :
    lastTransferFirstOwner (history hk i) = some i := rfl

theorem equal_logs (hk : 0 < k) (i j : Fin k) :
    events (history hk i) = events (history hk j) := rfl

theorem anonymity (hk : 0 < k) :
    hasAnonymitySet sup (events (history hk (baseOwner hk))) k := by
  refine ⟨fun i => (history hk i, finalState hk i), id, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨accepted hk i, crypto hk i, ObsEquiv.refl _⟩
  · intro i j h
    have hr := congrArg (fun e : List (Tx (Toy' k)) × St (Toy' k) =>
      lastTransferFirstOwner e.1) h
    exact Option.some.inj hr
  · exact Function.injective_id
  · exact recipient hk

/-- Arbitrarily large finite counts, under per-history collision freedom. -/
theorem candidate (hk : 0 < k) : acceptedAnonymityCandidate (Toy' k) sup k :=
  ⟨history hk (baseOwner hk), finalState hk (baseOwner hk),
    accepted hk (baseOwner hk), crypto hk (baseOwner hk), anonymity hk⟩

end ManyRecipientToy

end LeanShieldedPool.KAnonymity

#print axioms LeanShieldedPool.KAnonymity.TwoRecipientToy.candidate_two
#print axioms LeanShieldedPool.KAnonymity.TwoRecipientToy.indistinguishable_under_hiding
#print axioms LeanShieldedPool.KAnonymity.ConstantCommitToy.not_cardinalityOnlyCandidate
#print axioms LeanShieldedPool.KAnonymity.TwoRecipientToy.crypto_cross_history
#print axioms LeanShieldedPool.KAnonymity.ManyRecipientToy.candidate
#print axioms LeanShieldedPool.KAnonymity.hasAnonymitySet.mono
#print axioms LeanShieldedPool.KAnonymity.hasAnonymitySet_zero
#print axioms LeanShieldedPool.KAnonymity.acceptedAnonymityCandidate.mono
