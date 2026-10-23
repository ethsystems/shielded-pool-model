import Merkle.ZeroDepth
import Exec.RangeRun

namespace Deposit.MainHashes
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

theorem verify_zero {Γ st} (leaf : Fp p)
    (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)
    (hm : «deposit-0.0.0::verify_merkle_proof» ∈ Γ.functions)
    (hroot : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ Γ.functions) :
    Omni p Γ st («deposit-0.0.0::verify_merkle_proof».call h![(20 : U 32)]
      h![leaf, leaf, (0 : U 32), indices, path])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ hm
  dsimp only [«deposit-0.0.0::verify_merkle_proof»]
  repeat' first
    | (apply bind_result (Merkle.ZeroDepth.root_zero_depth _ _ _ _ hroot); intro st')
    | run_step
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (leaf = leaf)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩

-- This is a composition theorem with explicit hash-execution premises.
-- It is not an unconditional accepting-main witness.
theorem main_from_hashes {Γ st} (owner : Fp p) (hash4 : Fp p → Fp p → Fp p → Fp p → Fp p)
    (hmain : «deposit-0.0.0::main» ∈ Γ.functions)
    (hrange : «std-1.0.0-beta.21::field::assert_max_bit_size» ∈ Γ.functions)
    (hverify : «deposit-0.0.0::verify_merkle_proof» ∈ Γ.functions)
    (hroot : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ Γ.functions)
    (howner : ∀ st, Omni p Γ st («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
      h![(⟨[0], rfl⟩ : List.Vector (Fp p) 1)]) (fun r => ∃ st', r = some (st', owner)))
    (hhash4 : ∀ st a b c d, Omni p Γ st («deposit-0.0.0::poseidon4».call h![] h![a,b,c,d])
      (fun r => ∃ st', r = some (st', hash4 a b c d))) :
    Omni p Γ st («deposit-0.0.0::main».call h![]
      h![hash4 0 0 owner 0, (0 : Fp p), (0 : Fp p), (0 : Fp p), hash4 owner 0 0 0,
        (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : Fp p), (0 : U 64), (0 : U 64), (0 : U 32),
        List.Vector.replicate 20 (0 : Fp p), List.Vector.replicate 20 false])
      (fun r => ∃ st', r = some (st', ())) := by
  apply call _ _ _ hmain
  dsimp only [«deposit-0.0.0::main»]
  repeat' first
    | apply bind_value (Exec.RangeRun.zero_range hrange)
    | (apply bind_result (howner _); intro st')
    | (apply bind_result (hhash4 _ _ _ _ _); intro st')
    | (apply bind_result (verify_zero _ _ _ hverify hroot); intro st')
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((1 : U 32), Tp.field)))
  all_goals try first | rfl | exact () | trivial
  all_goals try (change ((decide (hash4 0 0 owner 0 = hash4 0 0 owner 0)) == true) = true; simp)
  all_goals try (dsimp [mapToValHeapCondition]; exact ⟨_, rfl⟩)
  all_goals exact ⟨_, rfl⟩

#print axioms verify_zero
#print axioms main_from_hashes
end Deposit.MainHashes
