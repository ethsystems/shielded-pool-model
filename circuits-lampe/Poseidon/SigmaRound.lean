import Exec.ArrayOps
open Lampe
noir_def steps::sigma_step<N: u32>(y: & Array<Field, N: u32>, i: u32) -> Unit := {
  let t = (#_arrayIndex returning Field)((#_readRef returning Array<Field, N: u32>)(y), (#_cast returning u32)(i));
  let tt = (#_fMul returning Field)(t, t);
  let tttt = (#_fMul returning Field)(tt, tt);
  (y[i]: Field) = (#_fMul returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, N: u32>)(y), (#_cast returning u32)(i)), tttt);
  #_skip
}
namespace Poseidon.SigmaRound
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

def fifth {p} (x : Fp p) := x*((x*x)*(x*x))
def update {p n} (v : List.Vector (Fp p) n) (i : Nat) :=
  if h : i < n then v.set ⟨i,h⟩ (fifth (v.get ⟨i,h⟩)) else v

def acc {p n} (v : List.Vector (Fp p) n) : Nat → List.Vector (Fp p) n
  | 0 => v
  | i+1 => update (acc v i) i

def body {p} (n : U 32) (addr : Address) (i : U 32) :=
  («steps::sigma_step».fn.body (Tp.denote p) h![n]).body h![Ref.mk (.array .field n) addr .nil, i]

theorem step {p Γ} (n : U 32) (st : State p) (addr : Address)
    (v : List.Vector (Fp p) n.toNat) (i : U 32) (hi : i.toNat < n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) v) (body n addr i)
      (fun r => r = some (set st addr (tp := .array .field n) (update v i.toNat), ())) := by
  have hm : some (update v i.toNat) =
      (Lens.cons Lens.nil (Access.array i) : Lens (Tp.denote p) (.array .field n) .field).modify
        v (fifth (v.get ⟨i.toNat,hi⟩)) := by
    simp [Lens.modify, Access.modify, update, hi]
  unfold body
  dsimp only [«steps::sigma_step»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.ArrayOps.index _ i hi)
    | apply bind_value (Exec.ArrayOps.mul _ _)
    | exec_pure
    | apply Omni.skip
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.field,n)))
  all_goals try first | exact hi | rfl | trivial
  apply bind_modify (updated := update v i.toNat)
  · exact Finmap.lookup_insert _
  · exact hm
  apply Omni.skip
  change some (set (set st addr (tp := .array .field n) v) addr (tp := .array .field n) (update v i.toNat), ()) = _
  simp only [Exec.Heap.set, Finmap.insert_insert]

theorem loop {p Γ} (n : U 32) (st : State p) (addr : Address)
    (v : List.Vector (Fp p) n.toNat) :
    Omni p Γ (set st addr (tp := .array .field n) v) (.loop (0 : U 32) n (body n addr))
      (fun r => r = some (set st addr (tp := .array .field n) (acc v n.toNat), ())) := by
  apply Exec.Loop.loop_exact (0 : U 32) n
    (fun i => set st addr (tp := .array .field n) (acc v i)) (body n addr) (by change 0 ≤ n.toNat; omega)
  intro i _ hi
  exact step n st addr (acc v i.toNat) i hi

theorem sigma {p Γ st} (n : U 32) (v : List.Vector (Fp p) n.toNat)
    (hm : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::sigma».call h![n] h![v])
      (Accept st (tp := .array .field n) (acc v n.toNat)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::sigma»]
  apply bind_ref
  intro addr hfresh
  exec_pure
  exec_pure
  apply bind_value (loop n st addr v)
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk
  · exact Finmap.lookup_insert _
  exact ⟨_, rfl, keeps_fresh st addr (tp := .array .field n) _ hfresh⟩

#print axioms loop
#print axioms sigma
#print axioms step
end Poseidon.SigmaRound
