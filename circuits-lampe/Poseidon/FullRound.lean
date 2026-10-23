import Poseidon.AddRound
import Poseidon.SigmaRound
import Poseidon.Matrix
open Lampe
noir_def steps::full_round<T: u32, N: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, mds: Array<Array<Field, T: u32>, T: u32>, r: u8) -> Unit := {
  state = («poseidon-0.0.0»::poseidon::sigma<T: u32> as λ(Array<Field, T: u32>) -> Array<Field, T: u32>)((#_readRef returning Array<Field, T: u32>)(state));
  for i in (0: u32) .. uConst!(T: u32) do {
    (state[i]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(i)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uMul returning u32)(uConst!(T: u32), (#_cast returning u32)((#_uAdd returning u8)(r, (1: u8)))), i))));
    #_skip
  };
  state = («poseidon-0.0.0»::poseidon::apply_matrix<T: u32> as λ(Array<Array<Field, T: u32>, T: u32>, Array<Field, T: u32>) -> Array<Field, T: u32>)(mds, (#_readRef returning Array<Field, T: u32>)(state));
  #_skip
}
namespace Poseidon.FullRound
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def body {p} (t n : U 32) (addr : Address) (rc : List.Vector (Fp p) n.toNat)
    (mds : List.Vector (List.Vector (Fp p) t.toNat) t.toNat) (r : U 8) : Expr (Tp.denote p) .unit :=
  («steps::full_round».fn.body (Tp.denote p) h![t,n]).body h![Ref.mk (.array .field t) addr .nil,rc,mds,r]

def value {p} (t n : U 32) (rc : List.Vector (Fp p) n.toNat)
    (mds : List.Vector (List.Vector (Fp p) t.toNat) t.toNat) (r : U 8) (v : List.Vector (Fp p) t.toNat) :=
  Poseidon.Matrix.outer mds (Poseidon.AddRound.acc t n rc r (Poseidon.SigmaRound.acc v t.toNat) t.toNat) t.toNat

theorem run {p Γ} (t n : U 32) (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) n.toNat) (mds : List.Vector (List.Vector (Fp p) t.toNat) t.toNat)
    (r : U 8) (v : List.Vector (Fp p) t.toNat)
    (hb : Poseidon.AddRound.Bounds t n r)
    (hv : st.vals.lookup addr = some ⟨.array .field t,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (body t n addr rc mds r)
      (Cell st addr (tp := .array .field t) (value t n rc mds r v)) := by
  unfold body
  dsimp only [«steps::full_round»]
  atom
  apply bind_read hv
  apply bind_accept (Poseidon.SigmaRound.sigma t v hsigma)
  intro s1 hk1
  apply bind_cell (write s1 addr (tp := .array .field t) v _ (hk1.2 _ _ hv))
  intro s2 hv2 hf2
  atom
  atom
  apply bind_cell (Poseidon.AddRound.run t n s2 addr rc r _ hb hv2)
  intro s3 hv3 hf3
  atom
  apply bind_read hv3
  apply bind_accept (Poseidon.Matrix.matrix t mds _ hmatrix)
  intro s4 hk4
  apply bind_cell (write s4 addr (tp := .array .field t) _ _ (hk4.2 _ _ hv3))
  intro s5 hv5 hf5
  apply Omni.skip
  exact ⟨s5,rfl,hv5,frame_trans (frame_trans (frame_trans (frame_trans
    (frame_of_keeps addr hk1) hf2) hf3) (frame_of_keeps addr hk4)) hf5⟩

def acc {p} (t n : U 32) (rc : List.Vector (Fp p) n.toNat)
    (mds : List.Vector (List.Vector (Fp p) t.toNat) t.toNat) (v : List.Vector (Fp p) t.toNat) : Nat → List.Vector (Fp p) t.toNat
  | 0 => v
  | i+1 => value t n rc mds (i : U 8) (acc t n rc mds v i)

theorem loop {p Γ} (t n : U 32) (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) n.toNat) (mds : List.Vector (List.Vector (Fp p) t.toNat) t.toNat)
    (v : List.Vector (Fp p) t.toNat)
    (hb : ∀ r : U 8, r.toNat < 3 → Poseidon.AddRound.Bounds t n r)
    (hv : st.vals.lookup addr = some ⟨.array .field t,v⟩)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions) :
    Omni p Γ st (.loop (0 : U 8) (3 : U 8) (body t n addr rc mds))
      (Cell st addr (tp := .array .field t) (acc t n rc mds v 3)) := by
  apply loop_cell (tp := .array .field t) (0 : U 8) (3 : U 8) addr st (acc t n rc mds v) (body t n addr rc mds) (by decide) hv
  intro r s _ hr hval
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    run t n s addr rc mds r (acc t n rc mds v r.toNat) (hb r hr) hval hsigma hmatrix

#print axioms run
#print axioms loop
end Poseidon.FullRound
