import Poseidon.AddRound
open Lampe
noir_def rounds::add_init<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, i: u32) -> Unit := {
    (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)(i)));
  #_skip
}
noir_def rounds::add_mid<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, rf: u8, i: u32) -> Unit := {
    (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uMul returning u32)(uConst!(T: u32), (#_cast returning u32)((#_uDiv returning u8)(rf, (2: u8)))), i))));
  #_skip
}
noir_def rounds::add_after<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, rf: u8, rp: u8, r: u8, i: u32) -> Unit := {
      (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uAdd returning u32)((#_uAdd returning u32)((#_uMul returning u32)((#_cast returning u32)((#_uAdd returning u8)((#_uDiv returning u8)(rf, (2: u8)), (1: u8))), uConst!(T: u32)), (#_cast returning u32)(rp)), (#_uMul returning u32)((#_cast returning u32)(r), uConst!(T: u32))), i))));
  #_skip
}
noir_def rounds::witness<T: u32>(state: & Array<Field, T: u32>, i: u32) -> Unit := {
  (#_asWitness returning Unit)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)));
  #_skip
}
namespace Poseidon.Add2
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def initIdx (r : U 8) (i : U 32) : U 32 := i
def initBody {p} (addr : Address) (rc : List.Vector (Fp p) 72) (r : U 8) (i : U 32) : Expr (Tp.denote p) .unit :=
  («rounds::add_init».fn.body (Tp.denote p) h![(2 : U 32),(72 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,rc,i]
def initAcc {p} (rc : List.Vector (Fp p) 72) (r : U 8) (v : List.Vector (Fp p) 2) : Nat → List.Vector (Fp p) 2
  | 0 => v
  | k+1 => Poseidon.AddRound.update rc (initAcc rc r v k) k (initIdx r (k : U 32)).toNat

theorem initStep {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (v : List.Vector (Fp p) 2)
    (r : U 8) (hr : r.toNat < 3) (i : U 32) (hi : i.toNat < 2) :
    Omni p Γ (set st addr (tp := .array .field 2) v) (initBody addr rc r i)
      (fun res => res = some (set st addr (tp := .array .field 2) (Poseidon.AddRound.update rc v i.toNat (initIdx r i).toNat), ())) := by
  have hr32 : (r.toNat : U 32).toNat = r.toNat := Nat.mod_eq_of_lt (by omega)
  have hmul : (r.toNat : U 32).toNat * (2 : U 32).toNat < 2^32 := by rw [hr32]; change r.toNat*2<4294967296; omega
  have hmulnat : ((r.toNat : U 32)*2).toNat = r.toNat*2 := by
    rw [BitVec.toNat_mul,hr32]; exact Nat.mod_eq_of_lt (by change r.toNat*2<4294967296; omega)
  have hbase : (66 : U 32).toNat + ((r.toNat : U 32)*2).toNat < 2^32 := by rw [hmulnat]; change 66+r.toNat*2<4294967296; omega
  have hbasenat : ((66 : U 32)+(r.toNat : U 32)*2).toNat = 66+r.toNat*2 := by
    rw [BitVec.toNat_add,hmulnat]; exact Nat.mod_eq_of_lt (by change 66+r.toNat*2<4294967296; omega)
  have hj : (initIdx r i).toNat < 72 := by
    simp only [initIdx, BitVec.toNat_add, hmulnat]
    omega
  have hm : some (Poseidon.AddRound.update rc v i.toNat (initIdx r i).toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field 2) .field).modify
        v (v.get ⟨i.toNat,hi⟩ + rc.get ⟨(initIdx r i).toNat,hj⟩) := by
    simp [Lens.modify, Access.modify, Poseidon.AddRound.update, hi, hj]
  unfold initBody
  dsimp only [«rounds::add_init»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ i hi)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 72) _ (initIdx r i) hj)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (4 : U 8) 1 (by decide))
    | apply bind_value (Exec.UIntOps.mul (2 : U 32) 4 (by decide))
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (10 : U 32) 56 (by decide))
    | apply bind_value (Exec.UIntOps.mul (r.toNat : U 32) 2 hmul)
    | apply bind_value (Exec.UIntOps.add (66 : U 32) _ hbase)
    | (apply bind_value (Exec.UIntOps.add (8 : U 32) i (by change 8+i.toNat<4294967296; omega)))
    | (apply bind_value (Exec.UIntOps.add ((66 : U 32)+(r.toNat : U 32)*2) i (by rw [hbasenat]; omega)))
    | atom
  apply bind_modify (updated := Poseidon.AddRound.update rc v i.toNat (initIdx r i).toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field 2) v) addr (tp := .array .field 2) _, ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert, RefPath.modify]

theorem initLoop {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (r : U 8) (hr : r.toNat < 3) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩) :
    Omni p Γ st (.loop (0 : U 32) (2 : U 32) (initBody addr rc r))
      (Cell st addr (tp := .array .field 2) (initAcc rc r v 2)) := by
  have h : Omni p Γ (set st addr (tp := .array .field 2) v) (.loop (0 : U 32) (2 : U 32) (initBody addr rc r))
      (fun res => res = some (set st addr (tp := .array .field 2) (initAcc rc r v 2), ())) := by
    apply Exec.Loop.loop_exact (0 : U 32) (2 : U 32)
      (fun k => set st addr (tp := .array .field 2) (initAcc rc r v k)) (initBody addr rc r) (by decide)
    intro i _ hi
    simpa only [initAcc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      initStep st addr rc (initAcc rc r v i.toNat) r hr i hi
  rw [set_of_lookup st addr (tp := .array .field 2) v hv] at h
  refine Omni.consequence h ?_
  intro res hr
  exact ⟨_,hr,Finmap.lookup_insert _,frame_set st addr _⟩
#print axioms initStep
#print axioms initLoop

def midIdx (r : U 8) (i : U 32) : U 32 := 8+i
def midBody {p} (addr : Address) (rc : List.Vector (Fp p) 72) (r : U 8) (i : U 32) : Expr (Tp.denote p) .unit :=
  («rounds::add_mid».fn.body (Tp.denote p) h![(2 : U 32),(72 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,rc,(8 : U 8),i]
def midAcc {p} (rc : List.Vector (Fp p) 72) (r : U 8) (v : List.Vector (Fp p) 2) : Nat → List.Vector (Fp p) 2
  | 0 => v
  | k+1 => Poseidon.AddRound.update rc (midAcc rc r v k) k (midIdx r (k : U 32)).toNat

theorem midStep {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (v : List.Vector (Fp p) 2)
    (r : U 8) (hr : r.toNat < 3) (i : U 32) (hi : i.toNat < 2) :
    Omni p Γ (set st addr (tp := .array .field 2) v) (midBody addr rc r i)
      (fun res => res = some (set st addr (tp := .array .field 2) (Poseidon.AddRound.update rc v i.toNat (midIdx r i).toNat), ())) := by
  have hr32 : (r.toNat : U 32).toNat = r.toNat := Nat.mod_eq_of_lt (by omega)
  have hmul : (r.toNat : U 32).toNat * (2 : U 32).toNat < 2^32 := by rw [hr32]; change r.toNat*2<4294967296; omega
  have hmulnat : ((r.toNat : U 32)*2).toNat = r.toNat*2 := by
    rw [BitVec.toNat_mul,hr32]; exact Nat.mod_eq_of_lt (by change r.toNat*2<4294967296; omega)
  have hbase : (66 : U 32).toNat + ((r.toNat : U 32)*2).toNat < 2^32 := by rw [hmulnat]; change 66+r.toNat*2<4294967296; omega
  have hbasenat : ((66 : U 32)+(r.toNat : U 32)*2).toNat = 66+r.toNat*2 := by
    rw [BitVec.toNat_add,hmulnat]; exact Nat.mod_eq_of_lt (by change 66+r.toNat*2<4294967296; omega)
  have hj : (midIdx r i).toNat < 72 := by
    change (8+i.toNat)%4294967296 < 72
    omega
  have hm : some (Poseidon.AddRound.update rc v i.toNat (midIdx r i).toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field 2) .field).modify
        v (v.get ⟨i.toNat,hi⟩ + rc.get ⟨(midIdx r i).toNat,hj⟩) := by
    simp [Lens.modify, Access.modify, Poseidon.AddRound.update, hi, hj]
  unfold midBody
  dsimp only [«rounds::add_mid»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ i hi)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 72) _ (midIdx r i) hj)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (4 : U 8) 1 (by decide))
    | apply bind_value (Exec.UIntOps.mul (2 : U 32) 4 (by decide))
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (10 : U 32) 56 (by decide))
    | apply bind_value (Exec.UIntOps.mul (r.toNat : U 32) 2 hmul)
    | apply bind_value (Exec.UIntOps.add (66 : U 32) _ hbase)
    | (apply bind_value (Exec.UIntOps.add (8 : U 32) i (by change 8+i.toNat<4294967296; omega)))
    | (apply bind_value (Exec.UIntOps.add ((66 : U 32)+(r.toNat : U 32)*2) i (by rw [hbasenat]; omega)))
    | atom
  apply bind_modify (updated := Poseidon.AddRound.update rc v i.toNat (midIdx r i).toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field 2) v) addr (tp := .array .field 2) _, ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert, RefPath.modify]

theorem midLoop {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (r : U 8) (hr : r.toNat < 3) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩) :
    Omni p Γ st (.loop (0 : U 32) (2 : U 32) (midBody addr rc r))
      (Cell st addr (tp := .array .field 2) (midAcc rc r v 2)) := by
  have h : Omni p Γ (set st addr (tp := .array .field 2) v) (.loop (0 : U 32) (2 : U 32) (midBody addr rc r))
      (fun res => res = some (set st addr (tp := .array .field 2) (midAcc rc r v 2), ())) := by
    apply Exec.Loop.loop_exact (0 : U 32) (2 : U 32)
      (fun k => set st addr (tp := .array .field 2) (midAcc rc r v k)) (midBody addr rc r) (by decide)
    intro i _ hi
    simpa only [midAcc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      midStep st addr rc (midAcc rc r v i.toNat) r hr i hi
  rw [set_of_lookup st addr (tp := .array .field 2) v hv] at h
  refine Omni.consequence h ?_
  intro res hr
  exact ⟨_,hr,Finmap.lookup_insert _,frame_set st addr _⟩
#print axioms midStep
#print axioms midLoop

def afterIdx (r : U 8) (i : U 32) : U 32 := 10+56+((r.toNat : U 32)*2)+i
def afterBody {p} (addr : Address) (rc : List.Vector (Fp p) 72) (r : U 8) (i : U 32) : Expr (Tp.denote p) .unit :=
  («rounds::add_after».fn.body (Tp.denote p) h![(2 : U 32),(72 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,rc,(8 : U 8),(56 : U 8),r,i]
def afterAcc {p} (rc : List.Vector (Fp p) 72) (r : U 8) (v : List.Vector (Fp p) 2) : Nat → List.Vector (Fp p) 2
  | 0 => v
  | k+1 => Poseidon.AddRound.update rc (afterAcc rc r v k) k (afterIdx r (k : U 32)).toNat

theorem afterStep {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (v : List.Vector (Fp p) 2)
    (r : U 8) (hr : r.toNat < 3) (i : U 32) (hi : i.toNat < 2) :
    Omni p Γ (set st addr (tp := .array .field 2) v) (afterBody addr rc r i)
      (fun res => res = some (set st addr (tp := .array .field 2) (Poseidon.AddRound.update rc v i.toNat (afterIdx r i).toNat), ())) := by
  have hr32 : (r.toNat : U 32).toNat = r.toNat := Nat.mod_eq_of_lt (by omega)
  have hmul : (r.toNat : U 32).toNat * (2 : U 32).toNat < 2^32 := by rw [hr32]; change r.toNat*2<4294967296; omega
  have hmulnat : ((r.toNat : U 32)*2).toNat = r.toNat*2 := by
    rw [BitVec.toNat_mul,hr32]; exact Nat.mod_eq_of_lt (by change r.toNat*2<4294967296; omega)
  have hbase : (66 : U 32).toNat + ((r.toNat : U 32)*2).toNat < 2^32 := by rw [hmulnat]; change 66+r.toNat*2<4294967296; omega
  have hbasenat : ((66 : U 32)+(r.toNat : U 32)*2).toNat = 66+r.toNat*2 := by
    rw [BitVec.toNat_add,hmulnat]; exact Nat.mod_eq_of_lt (by change 66+r.toNat*2<4294967296; omega)
  have hj : (afterIdx r i).toNat < 72 := by
    change (((66 : U 32)+(r.toNat : U 32)*2)+i).toNat < 72
    rw [BitVec.toNat_add,hbasenat]
    omega
  have hm : some (Poseidon.AddRound.update rc v i.toNat (afterIdx r i).toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field 2) .field).modify
        v (v.get ⟨i.toNat,hi⟩ + rc.get ⟨(afterIdx r i).toNat,hj⟩) := by
    simp [Lens.modify, Access.modify, Poseidon.AddRound.update, hi, hj]
  unfold afterBody
  dsimp only [«rounds::add_after»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ i hi)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 72) _ (afterIdx r i) hj)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (4 : U 8) 1 (by decide))
    | apply bind_value (Exec.UIntOps.mul (2 : U 32) 4 (by decide))
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (10 : U 32) 56 (by decide))
    | apply bind_value (Exec.UIntOps.mul (r.toNat : U 32) 2 hmul)
    | apply bind_value (Exec.UIntOps.add (66 : U 32) _ hbase)
    | (apply bind_value (Exec.UIntOps.add (8 : U 32) i (by change 8+i.toNat<4294967296; omega)))
    | (apply bind_value (Exec.UIntOps.add ((66 : U 32)+(r.toNat : U 32)*2) i (by rw [hbasenat]; omega)))
    | atom
  apply bind_modify (updated := Poseidon.AddRound.update rc v i.toNat (afterIdx r i).toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field 2) v) addr (tp := .array .field 2) _, ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert, RefPath.modify]

theorem afterLoop {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (r : U 8) (hr : r.toNat < 3) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩) :
    Omni p Γ st (.loop (0 : U 32) (2 : U 32) (afterBody addr rc r))
      (Cell st addr (tp := .array .field 2) (afterAcc rc r v 2)) := by
  have h : Omni p Γ (set st addr (tp := .array .field 2) v) (.loop (0 : U 32) (2 : U 32) (afterBody addr rc r))
      (fun res => res = some (set st addr (tp := .array .field 2) (afterAcc rc r v 2), ())) := by
    apply Exec.Loop.loop_exact (0 : U 32) (2 : U 32)
      (fun k => set st addr (tp := .array .field 2) (afterAcc rc r v k)) (afterBody addr rc r) (by decide)
    intro i _ hi
    simpa only [afterAcc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      afterStep st addr rc (afterAcc rc r v i.toNat) r hr i hi
  rw [set_of_lookup st addr (tp := .array .field 2) v hv] at h
  refine Omni.consequence h ?_
  intro res hr
  exact ⟨_,hr,Finmap.lookup_insert _,frame_set st addr _⟩
#print axioms afterStep
#print axioms afterLoop
def witnessBody {p} (addr : Address) (i : U 32) : Expr (Tp.denote p) .unit :=
  («rounds::witness».fn.body (Tp.denote p) h![(2 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,i]
theorem witnessStep {p Γ} (st : State p) (addr : Address) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩) (i : U 32) (hi : i.toNat < 2) :
    Omni p Γ st (witnessBody addr i) (fun r => r = some (st,())) := by
  unfold witnessBody
  dsimp only [«rounds::witness»]
  apply bind_read hv
  apply bind_value (Exec.ArrayOps.cast32 i)
  apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) v i hi)
  apply bind_value (Exec.UIntOps.witness _)
  exact Omni.skip rfl

theorem witnessLoop {p Γ} (st : State p) (addr : Address) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩) :
    Omni p Γ st (.loop (0 : U 32) (2 : U 32) (witnessBody addr)) (fun r => r = some (st,())) := by
  apply Exec.Loop.loop_exact (0 : U 32) (2 : U 32) (fun _ => st) (witnessBody addr) (by decide)
  intro i _ hi
  exact witnessStep st addr v hv i hi
#print axioms witnessStep
#print axioms witnessLoop
end Poseidon.Add2
