import Poseidon.Hash2

namespace Controls.Withdraw
open Lampe Exec.Basic Exec.Heap Withdraw.HashGood Withdraw.Rules Poseidon.Hash2
set_option backward.isDefEq.respectTransparency false



theorem same_hash_2_fwd (st : State p) (a b : Fp p) :
    Omni p Γw st («poseidon-0.0.0::poseidon::bn254::hash_2».call h![]
      h![(⟨[a,b],rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', hash2v a b)) :=
  hash2 a b f3 (mem1 Withdraw.Lookup.hash_2_filter) (mem1 Withdraw.Lookup.hash_internal_filter) x5_3_fwd

#print axioms same_hash_2_fwd
end Controls.Withdraw
