import Poseidon.Permutation3
import Withdraw.Rules

/-!
The width-3 forward result in the withdraw environment (as `Poseidon.Permutation2` and
`Poseidon.Permutation5` for widths 2 and 5): the extracted
`permute<3, 81, 285>` at the x5_3 constants computes `Poseidon.Permutation3.f`, hence `x5_3`, the
extracted `hash_2`, and the withdraw `poseidon2` compute `hash2 a b = (f [0, a, b])[0]`.
-/

namespace Poseidon.Hash2
open Lampe Exec.Basic Exec.Heap Withdraw.HashGood Withdraw.Rules
set_option backward.isDefEq.respectTransparency false

def Perm3 (Γ : Env) (f : List.Vector (Fp p) 3 → List.Vector (Fp p) 3) : Prop :=
  ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::permute».call h![(3 : U 32),(81 : U 32),(285 : U 32)]
    h![((3 : Fp p),(8 : U 8),(57 : U 8),(5 : Fp p),Poseidon.Constants3.rc,Poseidon.Constants3.mds,
      Poseidon.Constants3.pre,Poseidon.Constants3.sparse,()),v]) (Accept st (f v))

theorem wrapper3 {Γ} (st : State p) (v : List.Vector (Fp p) 3)
    (f : List.Vector (Fp p) 3 → List.Vector (Fp p) 3) (hp : Perm3 Γ f)
    (hm : «poseidon-0.0.0::poseidon::bn254::perm::x5_3» ∈ Γ.functions)
    (hc : «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config» ∈ Γ.functions)
    (hconfig : «poseidon-0.0.0::poseidon::config» ∈ Γ.functions)
    (ha : «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (Accept st (f v)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_3»]
  apply bind_ref
  intro addr hfresh
  atom
  atom
  apply bind_value (Poseidon.Constants3.config hc hconfig ha)
  apply bind_read (Finmap.lookup_insert _)
  apply bind_accept (hp _ v)
  intro st1 hk
  apply bind_modify (updated := f v) (hk.2 addr _ (Finmap.lookup_insert _)) rfl
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk (Finmap.lookup_insert _)
  dsimp only [Accept, RefPath.get, RefPath.modify]
  refine ⟨_,rfl,?_⟩
  apply keeps_of_frame_fresh hfresh
  apply frame_trans (frame_of_keeps addr (keeps_fresh (tp := .array .field 3) st addr v hfresh))
  apply frame_trans (frame_of_keeps addr hk)
  exact frame_set (tp := .array .field 3) st1 addr (f v)

theorem internal2 {Γ st} (a b : Fp p)
    (f : List.Vector (Fp p) 3 → List.Vector (Fp p) 3)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(2 : U 32),(3 : U 32)]
      h![(⟨[a, b],rfl⟩ : List.Vector (Fp p) 2),
        FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name [] h![] ])
      (fun r => ∃ st', r = some (st',(f ⟨[0, a, b],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | (apply bind_result (hp _ _); intro st')
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | (apply bind_value (Exec.UIntOps.add _ _ (by decide)))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ _ (by decide)))
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((3 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals try
    apply Omni.consequence (Exec.ArrayOps.index (tp := .field) (n := 3) _ 0 (by decide))
    intro r hr
    subst r
    exact ⟨_,rfl⟩

theorem hash2 {Γ st} (a b : Fp p)
    (f : List.Vector (Fp p) 3 → List.Vector (Fp p) 3)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_2» ∈ Γ.functions)
    (hi : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_2».call h![]
      h![(⟨[a,b],rfl⟩ : List.Vector (Fp p) 2)])
      (fun r => ∃ st', r = some (st',(f ⟨[0,a,b],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_2»]
  atom
  atom
  exact internal2 a b f hi hp

/-- The pure width-3 permutation value (as for widths 2 and 5) over the x5_3 constants. -/
def f3 := Poseidon.Permutation3.f

/-- The value the extracted `hash_2([a, b])` computes. -/
def hash2v (a b : Fp p) : Fp p := (f3 ⟨[0, a, b], rfl⟩).get ⟨0, by decide⟩

theorem perm3w : Perm3 Γw f3 := by
  intro st v
  exact Poseidon.Permutation3.run st _ _ _ _ v (mem1 Withdraw.Lookup.permute_filter) (mem1 Withdraw.Lookup.sigma_filter)
    (mem1 Withdraw.Lookup.apply_matrix_filter) (mem3 Withdraw.Lookup.pow_32_filter) (mem3 Withdraw.Lookup.to_le_bits_filter)

theorem x5_3_fwd (s : State p) (v : List.Vector (Fp p) 3) :
    Omni p Γw s («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (fun r => ∃ st', r = some (st', f3 v)) := by
  apply Omni.consequence (wrapper3 s v f3 perm3w
    (mem1 Withdraw.Lookup.x5_3_filter) (mem1 Withdraw.Lookup.x5_3_config_filter) (mem1 Withdraw.Lookup.config_filter)
    (mem1 Withdraw.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem hash_2_fwd (st : State p) (a b : Fp p) :
    Omni p Γw st («poseidon-0.0.0::poseidon::bn254::hash_2».call h![]
      h![(⟨[a,b],rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', hash2v a b)) :=
  hash2 a b f3 (mem1 Withdraw.Lookup.hash_2_filter) (mem1 Withdraw.Lookup.hash_internal_filter) x5_3_fwd

theorem poseidon2_fwd (st : State p) (a b : Fp p) :
    Omni p Γw st («withdraw-0.0.0::poseidon2».call h![] h![a, b])
      (fun r => ∃ st', r = some (st', hash2v a b)) := by
  apply call _ _ _ (mem1 Withdraw.Lookup.poseidon2_filter)
  dsimp only [«withdraw-0.0.0::poseidon2»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((2 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact hash_2_fwd _ a b

#print axioms wrapper3
#print axioms internal2
#print axioms hash2
#print axioms perm3w
#print axioms x5_3_fwd
#print axioms hash_2_fwd
#print axioms poseidon2_fwd
end Poseidon.Hash2
