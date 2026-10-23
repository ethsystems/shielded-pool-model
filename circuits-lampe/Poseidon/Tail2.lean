import Poseidon.FullRound
import Poseidon.Add2
open Lampe
noir_def rounds::tail<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, mds: Array<Array<Field, T: u32>, T: u32>, rf: u8, rp: u8, r: u8) -> Unit := {
    state = («poseidon-0.0.0»::poseidon::sigma<T: u32> as λ(Array<Field, T: u32>) -> Array<Field, T: u32>)((#_readRef returning Array<Field, T: u32>)(state));
    for i in (0: u32) .. (#_arrayLen returning u32)((#_readRef returning Array<Field, T: u32>)(state)) do {
      (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uAdd returning u32)((#_uAdd returning u32)((#_uMul returning u32)((#_cast returning u32)((#_uAdd returning u8)((#_uDiv returning u8)(rf, (2: u8)), (1: u8))), uConst!(T: u32)), (#_cast returning u32)(rp)), (#_uMul returning u32)((#_cast returning u32)(r), uConst!(T: u32))), i))));
      #_skip
    };
    state = («poseidon-0.0.0»::poseidon::apply_matrix<T: u32> as λ(Array<Array<Field, T: u32>, T: u32>, Array<Field, T: u32>) -> Array<Field, T: u32>)(mds, (#_readRef returning Array<Field, T: u32>)(state));
    #_skip
}
namespace Poseidon.Tail2
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def body {p} (addr : Address) (rc : List.Vector (Fp p) 72)
    (mds : List.Vector (List.Vector (Fp p) 2) 2) (r : U 8) : Expr (Tp.denote p) .unit :=
  («rounds::tail».fn.body (Tp.denote p) h![(2 : U 32),(72 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,rc,mds,(8 : U 8),(56 : U 8),r]

def value {p} (rc : List.Vector (Fp p) 72)
    (mds : List.Vector (List.Vector (Fp p) 2) 2) (r : U 8) (v : List.Vector (Fp p) 2) :=
  Poseidon.Matrix.outer mds (Poseidon.Add2.afterAcc rc r (Poseidon.SigmaRound.acc v 2) 2) 2

theorem run {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (mds : List.Vector (List.Vector (Fp p) 2) 2)
    (r : U 8) (hr : r.toNat < 3) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (body addr rc mds r)
      (Cell st addr (tp := .array .field 2) (value rc mds r v)) := by
  unfold body
  dsimp only [«rounds::tail»]
  atom
  apply bind_read hv
  apply bind_accept (Poseidon.SigmaRound.sigma 2 v hsigma)
  intro s1 hk1
  apply bind_cell (write s1 addr (tp := .array .field 2) v _ (hk1.2 _ _ hv))
  intro s2 hv2 hf2
  atom
  apply bind_read hv2
  apply bind_value (Exec.UIntOps.array_len 2 _)
  apply bind_cell (Poseidon.Add2.afterLoop s2 addr rc r hr _ hv2)
  intro s3 hv3 hf3
  atom
  apply bind_read hv3
  apply bind_accept (Poseidon.Matrix.matrix 2 mds _ hmatrix)
  intro s4 hk4
  apply bind_cell (write s4 addr (tp := .array .field 2) _ _ (hk4.2 _ _ hv3))
  intro s5 hv5 hf5
  apply Omni.skip
  exact ⟨s5,rfl,hv5,frame_trans (frame_trans (frame_trans (frame_trans
    (frame_of_keeps addr hk1) hf2) hf3) (frame_of_keeps addr hk4)) hf5⟩

def acc {p} (rc : List.Vector (Fp p) 72)
    (mds : List.Vector (List.Vector (Fp p) 2) 2) (v : List.Vector (Fp p) 2) : Nat → List.Vector (Fp p) 2
  | 0 => v
  | i+1 => value rc mds (i : U 8) (acc rc mds v i)

theorem loop {p Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (mds : List.Vector (List.Vector (Fp p) 2) 2)
    (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (.loop (0 : U 8) (3 : U 8) (body addr rc mds))
      (Cell st addr (tp := .array .field 2) (acc rc mds v 3)) := by
  apply loop_cell (tp := .array .field 2) (0 : U 8) (3 : U 8) addr st (acc rc mds v) (body addr rc mds) (by decide) hv
  intro r s _ hr hval
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    run s addr rc mds r hr (acc rc mds v r.toNat) hval hsigma hmatrix

#print axioms run
#print axioms loop
end Poseidon.Tail2
