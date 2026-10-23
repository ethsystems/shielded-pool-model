import Poseidon.Permutation2
import Poseidon.Permutation5

namespace Deposit.Main
open Lampe Exec.Heap
abbrev p := Crypto.Bn254.prime
abbrev Γ := Deposit.MainPermutations.Γ

def f2 := Poseidon.Permutation2.f
def f5 := Poseidon.Permutation5.f

theorem remaining : Deposit.MainPermutations.Remaining :=
  ⟨f2, f5, Poseidon.Permutation2.perm, Poseidon.Permutation5.perm⟩

theorem main_accepting_execution (st : State p) :
    Omni p Γ st (Deposit.MainPermutations.mainCall f2 f5) (fun r => ∃ st', r = some (st', ())) :=
  Deposit.MainPermutations.main_from_permutations st f2 f5 Poseidon.Permutation2.perm Poseidon.Permutation5.perm

theorem range_nonvacuous (st : State p) :
    Omni p Γ st (Deposit.MainPermutations.mainCall f2 f5) (fun r => ∃ st', r = some (st', ())) ∧
      (0 : Fp p).val < 2^128 :=
  Deposit.MainPermutations.range_witness_from_permutations st f2 f5 Poseidon.Permutation2.perm Poseidon.Permutation5.perm

#print axioms remaining
#print axioms main_accepting_execution
#print axioms range_nonvacuous
end Deposit.Main
