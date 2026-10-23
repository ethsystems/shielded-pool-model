import Exec.UIntOps
open Lampe
noir_def steps::add_before<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, r: u8, i: u32) -> Unit := {
  (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uMul returning u32)(uConst!(T: u32), (#_cast returning u32)((#_uAdd returning u8)(r, (1: u8)))), i))));
  #_skip
}
namespace Poseidon.AddRound
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def offset (t : U 32) (r : U 8) : U 32 := t * ((r+1).toNat : U 32)
def idx (t : U 32) (r : U 8) (i : U 32) : U 32 := offset t r + i

def update {p tn nn} (rc : List.Vector (Fp p) nn) (v : List.Vector (Fp p) tn) (i j : Nat) :=
  if hi : i<tn then if hj : j<nn then v.set ⟨i,hi⟩ (v.get ⟨i,hi⟩ + rc.get ⟨j,hj⟩) else v else v

def acc {p} (t n : U 32) (rc : List.Vector (Fp p) n.toNat)
    (r : U 8) (v : List.Vector (Fp p) t.toNat) : Nat → List.Vector (Fp p) t.toNat
  | 0 => v
  | i+1 => update rc (acc t n rc r v i) i (idx t r (i : U 32)).toNat

def body {p} (t n : U 32) (addr : Address) (rc : List.Vector (Fp p) n.toNat) (r : U 8) (i : U 32) : Expr (Tp.denote p) .unit :=
  («steps::add_before».fn.body (Tp.denote p) h![t,n]).body h![Ref.mk (.array .field t) addr .nil, rc,r,i]

def Bounds (t n : U 32) (r : U 8) : Prop :=
  r.toNat+1 < 2^8 ∧ t.toNat*((r+1).toNat : U 32).toNat < 2^32 ∧
  ∀ i : U 32, i.toNat < t.toNat → (offset t r).toNat+i.toNat < 2^32 ∧ (idx t r i).toNat < n.toNat

theorem step {p Γ} (t n : U 32) (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) n.toNat) (v : List.Vector (Fp p) t.toNat)
    (r : U 8) (i : U 32) (hi : i.toNat < t.toNat) (hb : Bounds t n r) :
    Omni p Γ (set st addr (tp := .array .field t) v) (body t n addr rc r i)
      (fun res => res = some (set st addr (tp := .array .field t) (update rc v i.toNat (idx t r i).toNat), ())) := by
  have hj := (hb.2.2 i hi).2
  have hm : some (update rc v i.toNat (idx t r i).toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field t) .field).modify
        v (v.get ⟨i.toNat,hi⟩ + rc.get ⟨(idx t r i).toNat,hj⟩) := by
    simp [Lens.modify, Access.modify, update, hi, hj]
  unfold body
  dsimp only [«steps::add_before»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.ArrayOps.index _ i hi)
    | apply bind_value (Exec.ArrayOps.index _ (idx t r i) hj)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.UIntOps.add r 1 hb.1)
    | apply bind_value (Exec.UIntOps.mul t _ hb.2.1)
    | apply bind_value (Exec.UIntOps.add (offset t r) i (hb.2.2 i hi).1)
    | atom
  apply bind_modify (updated := update rc v i.toNat (idx t r i).toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field t) v) addr (tp := .array .field t) _, ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert, RefPath.modify]

theorem bounds2 (r : U 8) (hr : r.toNat < 3) : Bounds 2 72 r := by
  have hm : (r.toNat+1)%256 = r.toNat+1 := Nat.mod_eq_of_lt (by omega)
  have hm32 : (r.toNat+1)%4294967296 = r.toNat+1 := Nat.mod_eq_of_lt (by omega)
  have hp : (2*(r.toNat+1))%4294967296 = 2*(r.toNat+1) := Nat.mod_eq_of_lt (by omega)
  simp [Bounds, offset, idx, BitVec.toNat_add, BitVec.toNat_mul, hm, hm32, hp]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  constructor
  · omega
  · exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

theorem bounds5 (r : U 8) (hr : r.toNat < 3) : Bounds 5 100 r := by
  have hm : (r.toNat+1)%256 = r.toNat+1 := Nat.mod_eq_of_lt (by omega)
  have hm32 : (r.toNat+1)%4294967296 = r.toNat+1 := Nat.mod_eq_of_lt (by omega)
  have hp : (5*(r.toNat+1))%4294967296 = 5*(r.toNat+1) := Nat.mod_eq_of_lt (by omega)
  simp [Bounds, offset, idx, BitVec.toNat_add, BitVec.toNat_mul, hm, hm32, hp]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  constructor
  · omega
  · exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

theorem loop {p Γ} (t n : U 32) (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) n.toNat) (r : U 8) (v : List.Vector (Fp p) t.toNat)
    (hb : Bounds t n r) :
    Omni p Γ (set st addr (tp := .array .field t) v) (.loop (0 : U 32) t (body t n addr rc r))
      (fun res => res = some (set st addr (tp := .array .field t) (acc t n rc r v t.toNat), ())) := by
  apply Exec.Loop.loop_exact (0 : U 32) t
    (fun i => set st addr (tp := .array .field t) (acc t n rc r v i))
    (body t n addr rc r) (by change 0 ≤ t.toNat; omega)
  intro i _ hi
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using step t n st addr rc (acc t n rc r v i.toNat) r i hi hb

theorem run {p Γ} (t n : U 32) (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) n.toNat) (r : U 8) (v : List.Vector (Fp p) t.toNat)
    (hb : Bounds t n r) (hv : st.vals.lookup addr = some ⟨.array .field t,v⟩) :
    Omni p Γ st (.loop (0 : U 32) t (body t n addr rc r))
      (Cell st addr (tp := .array .field t) (acc t n rc r v t.toNat)) := by
  have h := loop t n st addr rc r v hb (Γ := Γ)
  rw [set_of_lookup st addr (tp := .array .field t) v hv] at h
  refine Omni.consequence h ?_
  intro res hr
  exact ⟨_,hr,Finmap.lookup_insert _,frame_set st addr _⟩

#print axioms bounds2
#print axioms bounds5
#print axioms loop
#print axioms run
#print axioms step
end Poseidon.AddRound
