import Poseidon.Wrappers
namespace Poseidon.Hash
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

theorem internal1 {Γ st} (a : Fp p)
    (f : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(1 : U 32),(2 : U 32)]
      h![(⟨[a],rfl⟩ : List.Vector (Fp p) 1),
        FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_2».name [] h![] ])
      (fun r => ∃ st', r = some (st',(f ⟨[0, a],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | (apply bind_result (hp _ _); intro st')
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | (apply bind_value (Exec.UIntOps.add _ _ (by decide)))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 1) _ _ (by decide)))
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((2 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals try
    apply Omni.consequence (Exec.ArrayOps.index (tp := .field) (n := 2) _ 0 (by decide))
    intro r hr
    subst r
    exact ⟨_,rfl⟩

#print axioms internal1

theorem internal4 {Γ st} (a b c d : Fp p)
    (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_internal».call h![(4 : U 32),(5 : U 32)]
      h![(⟨[a, b, c, d],rfl⟩ : List.Vector (Fp p) 4),
        FuncRef.decl «poseidon-0.0.0::poseidon::bn254::perm::x5_5».name [] h![] ])
      (fun r => ∃ st', r = some (st',(f ⟨[0, a, b, c, d],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_internal»]
  repeat' first
    | (apply bind_result (hp _ _); intro st')
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | (apply bind_value (Exec.UIntOps.add _ _ (by decide)))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 4) _ _ (by decide)))
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((5 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals try
    apply Omni.consequence (Exec.ArrayOps.index (tp := .field) (n := 5) _ 0 (by decide))
    intro r hr
    subst r
    exact ⟨_,rfl⟩

#print axioms internal4


theorem hash1 {Γ st} (a : Fp p)
    (f : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_1» ∈ Γ.functions)
    (hi : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[a],rfl⟩ : List.Vector (Fp p) 1)])
      (fun r => ∃ st', r = some (st',(f ⟨[0,a],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_1»]
  atom
  atom
  exact internal1 a f hi hp

#print axioms hash1

theorem hash4 {Γ st} (a b c d : Fp p)
    (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hm : «poseidon-0.0.0::poseidon::bn254::hash_4» ∈ Γ.functions)
    (hi : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_4».call h![]
      h![(⟨[a,b,c,d],rfl⟩ : List.Vector (Fp p) 4)])
      (fun r => ∃ st', r = some (st',(f ⟨[0,a,b,c,d],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::bn254::hash_4»]
  atom
  atom
  exact internal4 a b c d f hi hp

#print axioms hash4

theorem poseidon4 {Γ st} (a b c d : Fp p)
    (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hm : «deposit-0.0.0::poseidon4» ∈ Γ.functions)
    (hh : «poseidon-0.0.0::poseidon::bn254::hash_4» ∈ Γ.functions)
    (hi : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ Γ.functions)
    (hp : ∀ st v, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (fun r => ∃ st', r = some (st', f v))) :
    Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a,b,c,d])
      (fun r => ∃ st', r = some (st',(f ⟨[0,a,b,c,d],rfl⟩).get ⟨0,by decide⟩)) := by
  apply call _ _ _ hm
  dsimp only [«deposit-0.0.0::poseidon4»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((4 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact hash4 a b c d f hh hi hp

#print axioms poseidon4
end Poseidon.Hash
