import Exec.Loop
namespace Exec.Heap
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false

def set {p tp} (st : State p) (addr : Address) (v : Tp.denote p tp) : State p :=
  ⟨st.vals.insert addr ⟨tp, v⟩, st.lambdas⟩

def Keeps {p} (st st' : State p) : Prop :=
  st'.lambdas = st.lambdas ∧ ∀ addr v, st.vals.lookup addr = some v → st'.vals.lookup addr = some v

theorem keeps_refl {p} (st : State p) : Keeps st st := ⟨rfl, fun _ _ h => h⟩

theorem keeps_trans {p} {a b c : State p} (h : Keeps a b) (h' : Keeps b c) : Keeps a c :=
  ⟨h'.1.trans h.1, fun addr v hv => h'.2 addr v (h.2 addr v hv)⟩

theorem keeps_fresh {p tp} (st : State p) (addr : Address) (v : Tp.denote p tp)
    (hfresh : addr ∉ st.vals) : Keeps st (set st addr v) := by
  refine ⟨rfl, ?_⟩
  intro a val hv
  have hne : a ≠ addr := by
    intro h; subst a
    exact hfresh (Finmap.mem_of_lookup_eq_some hv)
  exact (Finmap.lookup_insert_of_ne _ hne).trans hv

def Accept {p tp} (st : State p) (v : Tp.denote p tp) (r : Option (State p × Tp.denote p tp)) : Prop :=
  ∃ st', r = some (st', v) ∧ Keeps st st'

theorem bind_accept {p Γ st tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {v Q}
    (he : Omni p Γ st e (Accept st v))
    (hb : ∀ st', Keeps st st' → Omni p Γ st' (b v) Q) :
    Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn he
  · rintro _ _ ⟨st', h, hk⟩
    cases Option.some.inj h
    exact hb _ hk
  · rintro ⟨_, h, _⟩; cases h

def Frame {p} (addr : Address) (st st' : State p) : Prop :=
  st'.lambdas = st.lambdas ∧ ∀ a v, a ≠ addr → st.vals.lookup a = some v → st'.vals.lookup a = some v

theorem frame_refl {p} (addr : Address) (st : State p) : Frame addr st st :=
  ⟨rfl, fun _ _ _ h => h⟩

theorem frame_of_keeps {p} {st st' : State p} (addr : Address) (h : Keeps st st') : Frame addr st st' :=
  ⟨h.1, fun a v _ hv => h.2 a v hv⟩

theorem frame_trans {p addr} {a b c : State p} (h : Frame addr a b) (h' : Frame addr b c) : Frame addr a c :=
  ⟨h'.1.trans h.1, fun a v hne hv => h'.2 a v hne (h.2 a v hne hv)⟩

theorem frame_set {p tp} (st : State p) (addr : Address) (v : Tp.denote p tp) : Frame addr st (set st addr v) :=
  ⟨rfl, fun a val hne hv => (Finmap.lookup_insert_of_ne _ hne).trans hv⟩

theorem keeps_of_frame_fresh {p addr} {st st' : State p}
    (hf : addr ∉ st.vals) (h : Frame addr st st') : Keeps st st' := by
  refine ⟨h.1, ?_⟩
  intro a v hv
  apply h.2 a v ?_ hv
  intro heq; subst a
  exact hf (Finmap.mem_of_lookup_eq_some hv)

theorem set_of_lookup {p tp} (st : State p) (addr : Address) (v : Tp.denote p tp)
    (hv : st.vals.lookup addr = some ⟨tp,v⟩) : set st addr v = st := by
  have hm : st.vals.insert addr ⟨tp,v⟩ = st.vals := by
    apply Finmap.ext_lookup
    intro a
    by_cases h : a = addr
    · subst a; simp only [Finmap.lookup_insert, hv]
    · exact Finmap.lookup_insert_of_ne _ h
  cases st
  simp_all [set]

def Cell {p tp} (st : State p) (addr : Address) (v : Tp.denote p tp)
    (r : Option (State p × Unit)) : Prop :=
  ∃ st', r = some (st', ()) ∧ st'.vals.lookup addr = some ⟨tp,v⟩ ∧ Frame addr st st'

theorem bind_cell {p Γ st tp tp'} {addr : Address} {e : Expr (Tp.denote p) .unit}
    {b : Unit → Expr (Tp.denote p) tp'} {v : Tp.denote p tp} {Q}
    (he : Omni p Γ st e (Cell st addr v))
    (hb : ∀ st', st'.vals.lookup addr = some ⟨tp,v⟩ → Frame addr st st' → Omni p Γ st' (b ()) Q) :
    Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn he
  · rintro _ _ ⟨st', h, hv, hf⟩
    cases Option.some.inj h
    exact hb _ hv hf
  · rintro ⟨_, h, _⟩; cases h

theorem write {p Γ tp} (st : State p) (addr : Address) (old v : Tp.denote p tp)
    (hv : st.vals.lookup addr = some ⟨tp,old⟩) :
    Omni p Γ st (.modifyLens (Ref.mk tp addr .nil) v .nil) (Cell st addr v) := by
  apply Omni.callBuiltin
  apply Builtin.modifyLensOmni.ok (hr := rfl)
  · exact hv
  · rfl
  · rfl
  · rfl
  exact ⟨_, rfl, Finmap.lookup_insert _, frame_set st addr v⟩

theorem loop_cell {p Γ tp w} (lo hi : U w) (addr : Address) (st : State p)
    (value : Nat → Tp.denote p tp) (body : U w → Expr (Tp.denote p) .unit)
    (hle : lo ≤ hi) (hv : st.vals.lookup addr = some ⟨tp,value lo.toNat⟩)
    (step : ∀ i s, lo ≤ i → i < hi → s.vals.lookup addr = some ⟨tp,value i.toNat⟩ →
      Omni p Γ s (body i) (Cell s addr (value (i.toNat+1)))) :
    Omni p Γ st (.loop lo hi body) (Cell st addr (value hi.toNat)) := by
  refine Omni.consequence (Exec.Loop.loop_inv lo hi body
    (fun i s => s.vals.lookup addr = some ⟨tp,value i.toNat⟩ ∧ Frame addr st s) ?_ hle
    ⟨hv,frame_refl addr st⟩) ?_
  · intro i s hil hih hinv
    refine Omni.consequence (step i s hil hih hinv.1) ?_
    rintro r ⟨s',hr,hv',hf⟩
    refine ⟨s',hr,?_,frame_trans hinv.2 hf⟩
    have hvnat : (i+1).toNat = i.toNat+1 := by
      have hlt : i.toNat < hi.toNat := hih
      have hh := hi.isLt
      have hw : 1 < 2^w := by omega
      change (i.toNat + 1 % 2^w) % 2^w = i.toNat+1
      rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]
    simpa only [hvnat] using hv'
  · rintro r ⟨s,hr,hv',hf⟩; exact ⟨s,hr,hv',hf⟩

macro "atom" : tactic => `(tactic| first
  | refine bind_value (Omni.fn rfl) ?_
  | refine bind_value (Omni.constU rfl) ?_
  | refine bind_value (Omni.litU rfl) ?_
  | refine bind_value (Omni.litField rfl) ?_
  | refine bind_value (Omni.var rfl) ?_
  | refine bind_value (Omni.skip rfl) ?_)

theorem frame_insert {p tp main} {st st' : State p} (hf : Frame main st st')
    (addr : Address) (v : Tp.denote p tp) (ha : addr = main ∨ addr ∉ st.vals) :
    Frame main st (set st' addr v) := by
  refine ⟨hf.1, ?_⟩
  intro a val hne hv
  have hneq : a ≠ addr := by
    intro heq; subst a
    rcases ha with h | h
    · exact hne h
    · exact h (Finmap.mem_of_lookup_eq_some hv)
  exact (Finmap.lookup_insert_of_ne _ hneq).trans (hf.2 a val hne hv)

theorem not_mem_of_keeps {p} {st st' : State p} (h : Keeps st st') {a : Address}
    (ha : a ∉ st'.vals) : a ∉ st.vals := by
  intro hm
  obtain ⟨v,hv⟩ := Finmap.mem_iff.mp hm
  exact ha (Finmap.mem_of_lookup_eq_some (h.2 a v hv))

#print axioms frame_insert
#print axioms not_mem_of_keeps
#print axioms write
#print axioms loop_cell
#print axioms frame_refl
#print axioms frame_of_keeps
#print axioms frame_trans
#print axioms frame_set
#print axioms keeps_of_frame_fresh
#print axioms set_of_lookup
#print axioms bind_cell
#print axioms keeps_refl
#print axioms keeps_trans
#print axioms keeps_fresh
#print axioms bind_accept
end Exec.Heap
