import Poseidon.Constants2
import Poseidon.Constants5
namespace Poseidon.Wrappers
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def Perm2 (Γ : Env) (f : List.Vector (Fp p) 2 → List.Vector (Fp p) 2) : Prop :=
  ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::permute».call h![(2 : U 32),(72 : U 32),(168 : U 32)]
    h![((2 : Fp p),(8 : U 8),(56 : U 8),(5 : Fp p),Poseidon.Constants2.rc,Poseidon.Constants2.mds,
      Poseidon.Constants2.pre,Poseidon.Constants2.sparse,()),v]) (Accept st (f v))

theorem wrapper2 {Γ} (st : State p) (v : List.Vector (Fp p) 2)
    (f : List.Vector (Fp p) 2 → List.Vector (Fp p) 2) (hp : Perm2 Γ f)
    (hm : «poseidon-0.0.0::poseidon::bn254::perm::x5_2» ∈ Γ.functions)
    (hc : «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» ∈ Γ.functions)
    (hconfig : «poseidon-0.0.0::poseidon::config» ∈ Γ.functions)
    (ha : «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v])
      (Accept st (f v)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_2»]
  apply bind_ref
  intro addr hfresh
  atom
  atom
  apply bind_value (Poseidon.Constants2.config hc hconfig ha)
  apply bind_read (Finmap.lookup_insert _)
  apply bind_accept (hp _ v)
  intro st1 hk
  apply bind_modify (updated := f v) (hk.2 addr _ (Finmap.lookup_insert _)) rfl
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk (Finmap.lookup_insert _)
  dsimp only [Accept, RefPath.get, RefPath.modify]
  refine ⟨_,rfl,?_⟩
  apply keeps_of_frame_fresh hfresh
  apply frame_trans (frame_of_keeps addr (keeps_fresh (tp := .array .field 2) st addr v hfresh))
  apply frame_trans (frame_of_keeps addr hk)
  exact frame_set (tp := .array .field 2) st1 addr (f v)

#print axioms wrapper2

def Perm5 (Γ : Env) (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5) : Prop :=
  ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::permute».call h![(5 : U 32),(100 : U 32),(540 : U 32)]
    h![((5 : Fp p),(8 : U 8),(60 : U 8),(5 : Fp p),Poseidon.Constants5.rc,Poseidon.Constants5.mds,
      Poseidon.Constants5.pre,Poseidon.Constants5.sparse,()),v]) (Accept st (f v))

theorem wrapper5 {Γ} (st : State p) (v : List.Vector (Fp p) 5)
    (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5) (hp : Perm5 Γ f)
    (hm : «poseidon-0.0.0::poseidon::bn254::perm::x5_5» ∈ Γ.functions)
    (hc : «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config» ∈ Γ.functions)
    (hconfig : «poseidon-0.0.0::poseidon::config» ∈ Γ.functions)
    (ha : «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (Accept st (f v)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::perm::x5_5»]
  apply bind_ref
  intro addr hfresh
  atom
  atom
  apply bind_value (Poseidon.Constants5.config hc hconfig ha)
  apply bind_read (Finmap.lookup_insert _)
  apply bind_accept (hp _ v)
  intro st1 hk
  apply bind_modify (updated := f v) (hk.2 addr _ (Finmap.lookup_insert _)) rfl
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk (Finmap.lookup_insert _)
  dsimp only [Accept, RefPath.get, RefPath.modify]
  refine ⟨_,rfl,?_⟩
  apply keeps_of_frame_fresh hfresh
  apply frame_trans (frame_of_keeps addr (keeps_fresh (tp := .array .field 5) st addr v hfresh))
  apply frame_trans (frame_of_keeps addr hk)
  exact frame_set (tp := .array .field 5) st1 addr (f v)

#print axioms wrapper5

end Poseidon.Wrappers
