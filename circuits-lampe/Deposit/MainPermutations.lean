import Deposit.Members
import Deposit.Range
namespace Deposit.MainPermutations
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime
abbrev Γ := «deposit-0.0.0».env

def owner (f : List.Vector (Fp p) 2 → List.Vector (Fp p) 2) :=
  (f ⟨[0,0],rfl⟩).get ⟨0,by decide⟩
def hash4 (f : List.Vector (Fp p) 5 → List.Vector (Fp p) 5) (a b c d : Fp p) :=
  (f ⟨[0,a,b,c,d],rfl⟩).get ⟨0,by decide⟩

def mainCall (f2 : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (f5 : List.Vector (Fp p) 5 → List.Vector (Fp p) 5) :=
  «deposit-0.0.0::main».call h![]
    h![hash4 f5 0 0 (owner f2) 0, (0 : Fp p), (0 : Fp p), (0 : Fp p), hash4 f5 (owner f2) 0 0 0,
      (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : U 64), (0 : U 64), (0 : U 32),
      List.Vector.replicate 20 (0 : Fp p), List.Vector.replicate 20 false]

theorem hashes_from_permutations
    (f2 : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (f5 : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hp2 : Poseidon.Wrappers.Perm2 Γ f2) (hp5 : Poseidon.Wrappers.Perm5 Γ f5) :
    (∀ st, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[0],rfl⟩ : List.Vector (Fp p) 1)]) (fun r => ∃ st', r = some (st',owner f2))) ∧
    (∀ st a b c d, Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a,b,c,d])
      (fun r => ∃ st', r = some (st',hash4 f5 a b c d))) := by
  constructor
  · intro st
    apply Poseidon.Hash.hash1 0 f2 Deposit.Members.hash1 Deposit.Members.internal
    intro s v
    apply Omni.consequence (Poseidon.Wrappers.wrapper2 s v f2 hp2 Deposit.Members.wrapper2
      Deposit.Members.config2 Deposit.Members.config Deposit.Members.alpha)
    rintro r ⟨s',h,_⟩
    exact ⟨s',h⟩
  · intro st a b c d
    apply Poseidon.Hash.poseidon4 a b c d f5 Deposit.Members.poseidon4 Deposit.Members.hash4 Deposit.Members.internal
    intro s v
    apply Omni.consequence (Poseidon.Wrappers.wrapper5 s v f5 hp5 Deposit.Members.wrapper5
      Deposit.Members.config5 Deposit.Members.config Deposit.Members.alpha)
    rintro r ⟨s',h,_⟩
    exact ⟨s',h⟩

theorem main_from_permutations (st : State p)
    (f2 : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (f5 : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hp2 : Poseidon.Wrappers.Perm2 Γ f2) (hp5 : Poseidon.Wrappers.Perm5 Γ f5) :
    Omni p Γ st (mainCall f2 f5) (fun r => ∃ st', r = some (st',())) := by
  obtain ⟨howner,hh⟩ := hashes_from_permutations f2 f5 hp2 hp5
  exact Deposit.MainHashes.main_from_hashes (owner f2) (hash4 f5) Deposit.Members.main Deposit.Members.range
    Deposit.Members.verify Deposit.Members.root howner hh

theorem range_witness_from_permutations (st : State p)
    (f2 : List.Vector (Fp p) 2 → List.Vector (Fp p) 2)
    (f5 : List.Vector (Fp p) 5 → List.Vector (Fp p) 5)
    (hp2 : Poseidon.Wrappers.Perm2 Γ f2) (hp5 : Poseidon.Wrappers.Perm5 Γ f5) :
    Omni p Γ st (mainCall f2 f5) (fun r => ∃ st', r = some (st',())) ∧
      (0 : Fp p).val < 2^128 := by
  have h := main_from_permutations st f2 f5 hp2 hp5
  refine ⟨h,?_⟩
  exact Deposit.Range.accepting_main_amount_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    (by rintro ⟨_,hfail⟩; cases hfail)

def Remaining : Prop :=
  ∃ f2 f5, Poseidon.Wrappers.Perm2 Γ f2 ∧ Poseidon.Wrappers.Perm5 Γ f5

#print axioms hashes_from_permutations
#print axioms main_from_permutations
#print axioms range_witness_from_permutations
end Deposit.MainPermutations
