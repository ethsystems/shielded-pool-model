import Poseidon.Tail2
import Poseidon.Add3
open Lampe
namespace Poseidon.Tail3
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def body {p} (addr : Address) (rc : List.Vector (Fp p) 81)
    (mds : List.Vector (List.Vector (Fp p) 3) 3) (r : U 8) : Expr (Tp.denote p) .unit :=
  («rounds::tail».fn.body (Tp.denote p) h![(3 : U 32),(81 : U 32)]).body h![Ref.mk (.array .field 3) addr .nil,rc,mds,(8 : U 8),(57 : U 8),r]

def value {p} (rc : List.Vector (Fp p) 81)
    (mds : List.Vector (List.Vector (Fp p) 3) 3) (r : U 8) (v : List.Vector (Fp p) 3) :=
  Poseidon.Matrix.outer mds (Poseidon.Add3.afterAcc rc r (Poseidon.SigmaRound.acc v 3) 3) 3

theorem run {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 81) (mds : List.Vector (List.Vector (Fp p) 3) 3)
    (r : U 8) (hr : r.toNat < 3) (v : List.Vector (Fp p) 3)
    (hv : st.vals.lookup addr = some ⟨.array .field 3,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (body addr rc mds r)
      (Cell st addr (tp := .array .field 3) (value rc mds r v)) := by
  unfold body
  dsimp only [«rounds::tail»]
  atom
  apply bind_read hv
  apply bind_accept (Poseidon.SigmaRound.sigma 3 v hsigma)
  intro s1 hk1
  apply bind_cell (write s1 addr (tp := .array .field 3) v _ (hk1.2 _ _ hv))
  intro s2 hv2 hf2
  atom
  apply bind_read hv2
  apply bind_value (Exec.UIntOps.array_len 3 _)
  apply bind_cell (Poseidon.Add3.afterLoop s2 addr rc r hr _ hv2)
  intro s3 hv3 hf3
  atom
  apply bind_read hv3
  apply bind_accept (Poseidon.Matrix.matrix 3 mds _ hmatrix)
  intro s4 hk4
  apply bind_cell (write s4 addr (tp := .array .field 3) _ _ (hk4.2 _ _ hv3))
  intro s5 hv5 hf5
  apply Omni.skip
  exact ⟨s5,rfl,hv5,frame_trans (frame_trans (frame_trans (frame_trans
    (frame_of_keeps addr hk1) hf2) hf3) (frame_of_keeps addr hk4)) hf5⟩

def acc {p} (rc : List.Vector (Fp p) 81)
    (mds : List.Vector (List.Vector (Fp p) 3) 3) (v : List.Vector (Fp p) 3) : Nat → List.Vector (Fp p) 3
  | 0 => v
  | i+1 => value rc mds (i : U 8) (acc rc mds v i)

theorem loop {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 81) (mds : List.Vector (List.Vector (Fp p) 3) 3)
    (v : List.Vector (Fp p) 3)
    (hv : st.vals.lookup addr = some ⟨.array .field 3,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (.loop (0 : U 8) (3 : U 8) (body addr rc mds))
      (Cell st addr (tp := .array .field 3) (acc rc mds v 3)) := by
  apply loop_cell (tp := .array .field 3) (0 : U 8) (3 : U 8) addr st (acc rc mds v) (body addr rc mds) (by decide) hv
  intro r s _ hr hval
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    run s addr rc mds r hr (acc rc mds v r.toNat) hval hsigma hmatrix

#print axioms run
#print axioms loop
end Poseidon.Tail3
