import Exec.ArrayOps
open Lampe
noir_def steps::matrix_step<N: u32>(out: & Array<Field, N: u32>, matrix: Array<Array<Field, N: u32>, N: u32>, vec: Array<Field, N: u32>, i: u32, j: u32) -> Unit := {
  (out[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, N: u32>)(out), (#_cast returning u32)(i)), (#_fMul returning Field)((#_arrayIndex returning Field)(vec, (#_cast returning u32)(j)), (#_arrayIndex returning Field)((#_arrayIndex returning Array<Field, N: u32>)(matrix, (#_cast returning u32)(j)), (#_cast returning u32)(i))));
  #_skip
}
noir_def steps::matrix_row<N: u32>(out: & Array<Field, N: u32>, matrix: Array<Array<Field, N: u32>, N: u32>, vec: Array<Field, N: u32>, i: u32) -> Unit := {
  for j in (0: u32) .. uConst!(N: u32) do {
    (out[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, N: u32>)(out), (#_cast returning u32)(i)), (#_fMul returning Field)((#_arrayIndex returning Field)(vec, (#_cast returning u32)(j)), (#_arrayIndex returning Field)((#_arrayIndex returning Array<Field, N: u32>)(matrix, (#_cast returning u32)(j)), (#_cast returning u32)(i))));
    #_skip
  };
  #_skip
}
namespace Poseidon.Matrix
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def update {p n} (m : List.Vector (List.Vector (Fp p) n) n)
    (v out : List.Vector (Fp p) n) (i j : Nat) : List.Vector (Fp p) n :=
  if hi : i<n then if hj : j<n then
    out.set ⟨i,hi⟩ (out.get ⟨i,hi⟩ + v.get ⟨j,hj⟩ * (m.get ⟨j,hj⟩).get ⟨i,hi⟩)
  else out else out

def inner {p n} (m : List.Vector (List.Vector (Fp p) n) n)
    (v out : List.Vector (Fp p) n) (i : Nat) : Nat → List.Vector (Fp p) n
  | 0 => out
  | j+1 => update m v (inner m v out i j) i j

def outer {p n} (m : List.Vector (List.Vector (Fp p) n) n)
    (v : List.Vector (Fp p) n) : Nat → List.Vector (Fp p) n
  | 0 => List.Vector.replicate n 0
  | i+1 => inner m v (outer m v i) i n

def body {p} (n : U 32) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v : List.Vector (Fp p) n.toNat) (i j : U 32) :=
  («steps::matrix_step».fn.body (Tp.denote p) h![n]).body h![Ref.mk (.array .field n) addr .nil,m,v,i,j]

def row {p} (n : U 32) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v : List.Vector (Fp p) n.toNat) (i : U 32) :=
  («steps::matrix_row».fn.body (Tp.denote p) h![n]).body h![Ref.mk (.array .field n) addr .nil,m,v,i]

theorem step {p Γ} (n : U 32) (st : State p) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v out : List.Vector (Fp p) n.toNat) (i j : U 32)
    (hi : i.toNat < n.toNat) (hj : j.toNat < n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) out) (body n addr m v i j)
      (fun r => r = some (set st addr (tp := .array .field n) (update m v out i.toNat j.toNat), ())) := by
  have hm : some (update m v out i.toNat j.toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field n) .field).modify
        out (out.get ⟨i.toNat,hi⟩ + v.get ⟨j.toNat,hj⟩ * (m.get ⟨j.toNat,hj⟩).get ⟨i.toNat,hi⟩) := by
    simp [Lens.modify, Access.modify, update, hi, hj]
  unfold body
  dsimp only [«steps::matrix_step»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.ArrayOps.index _ i hi)
    | apply bind_value (Exec.ArrayOps.index _ j hj)
    | apply bind_value (Exec.ArrayOps.mul _ _)
    | apply bind_value (Exec.ArrayOps.add _ _)
  apply bind_modify (updated := update m v out i.toNat j.toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field n) out) addr (tp := .array .field n) (update m v out i.toNat j.toNat), ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert]

theorem inner_loop {p Γ} (n : U 32) (st : State p) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v out : List.Vector (Fp p) n.toNat) (i : U 32) (hi : i.toNat < n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) out) (.loop (0 : U 32) n (body n addr m v i))
      (fun r => r = some (set st addr (tp := .array .field n) (inner m v out i.toNat n.toNat), ())) := by
  apply Exec.Loop.loop_exact (0 : U 32) n
    (fun j => set st addr (tp := .array .field n) (inner m v out i.toNat j))
    (body n addr m v i) (by change 0 ≤ n.toNat; omega)
  intro j _ hj
  exact step n st addr m v (inner m v out i.toNat j.toNat) i j hi hj

theorem row_run {p Γ} (n : U 32) (st : State p) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v out : List.Vector (Fp p) n.toNat) (i : U 32) (hi : i.toNat < n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) out) (row n addr m v i)
      (fun r => r = some (set st addr (tp := .array .field n) (inner m v out i.toNat n.toNat), ())) := by
  unfold row
  dsimp only [«steps::matrix_row»]
  exec_pure
  exec_pure
  apply bind_value (inner_loop n st addr m v out i hi)
  exact Omni.skip rfl

theorem outer_loop {p Γ} (n : U 32) (st : State p) (addr : Address)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v : List.Vector (Fp p) n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) (List.Vector.replicate n.toNat 0))
      (.loop (0 : U 32) n (row n addr m v))
      (fun r => r = some (set st addr (tp := .array .field n) (outer m v n.toNat), ())) := by
  apply Exec.Loop.loop_exact (0 : U 32) n
    (fun i => set st addr (tp := .array .field n) (outer m v i))
    (row n addr m v) (by change 0 ≤ n.toNat; omega)
  intro i _ hi
  exact row_run n st addr m v (outer m v i.toNat) i hi

theorem matrix {p Γ st} (n : U 32)
    (m : List.Vector (List.Vector (Fp p) n.toNat) n.toNat)
    (v : List.Vector (Fp p) n.toNat)
    (hm : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::apply_matrix».call h![n] h![m,v])
      (Accept st (tp := .array .field n) (outer m v n.toNat)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::apply_matrix»]
  exec_pure
  apply bind_value (v := List.Vector.replicate n.toNat (0 : Fp p))
  · apply Omni.callBuiltin
    exact Builtin.genericPureOmni.ok (a := (n,Tp.field)) True.intro rfl
  apply bind_ref
  intro addr hfresh
  exec_pure
  exec_pure
  apply bind_value (outer_loop n st addr m v)
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk
  · exact Finmap.lookup_insert _
  exact ⟨_, rfl, keeps_fresh st addr (tp := .array .field n) _ hfresh⟩

#print axioms inner_loop
#print axioms row_run
#print axioms outer_loop
#print axioms matrix
#print axioms step
end Poseidon.Matrix
