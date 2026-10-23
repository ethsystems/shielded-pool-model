import Transfer.HashDeterminism
import Poseidon.Hash2

/-!
Forward results and pinned values in the TRANSFER environment. The proofs are the withdraw
ones (`Withdraw.Rules` part 2, `Poseidon.Hash2`) with the transfer certificates (`Transfer.Lookup`); the pure
functions are the same: `Deposit.Commitment.ownerKey` (width 2), `Deposit.Commitment.hash4` (width 5) and
`Poseidon.Hash2.hash2v` (width 3). No claim about Poseidon's cryptographic properties.
-/

namespace Transfer.Forward
open Lampe Determinism Transfer.HashGood

abbrev p := Crypto.Bn254.prime

section
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false

theorem perm2t : Poseidon.Wrappers.Perm2 Γt Deposit.Main.f2 := by
  intro st v
  exact Poseidon.Permutation2.run st _ _ _ _ v (Withdraw.Rules.mem1 Transfer.Lookup.permute_filter) (Withdraw.Rules.mem1 Transfer.Lookup.sigma_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.apply_matrix_filter) (Withdraw.Rules.mem3 Transfer.Lookup.pow_32_filter) (Withdraw.Rules.mem3 Transfer.Lookup.to_le_bits_filter)

theorem perm5t : Poseidon.Wrappers.Perm5 Γt Deposit.Main.f5 := by
  intro st v
  exact Poseidon.Permutation5.run st _ _ _ _ v (Withdraw.Rules.mem1 Transfer.Lookup.permute_filter) (Withdraw.Rules.mem1 Transfer.Lookup.sigma_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.apply_matrix_filter) (Withdraw.Rules.mem3 Transfer.Lookup.pow_32_filter) (Withdraw.Rules.mem3 Transfer.Lookup.to_le_bits_filter)

theorem perm3t : Poseidon.Hash2.Perm3 Γt Poseidon.Hash2.f3 := by
  intro st v
  exact Poseidon.Permutation3.run st _ _ _ _ v (Withdraw.Rules.mem1 Transfer.Lookup.permute_filter) (Withdraw.Rules.mem1 Transfer.Lookup.sigma_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.apply_matrix_filter) (Withdraw.Rules.mem3 Transfer.Lookup.pow_32_filter) (Withdraw.Rules.mem3 Transfer.Lookup.to_le_bits_filter)

theorem x5_2_fwd (s : State p) (v : List.Vector (Fp p) 2) :
    Omni p Γt s («poseidon-0.0.0::poseidon::bn254::perm::x5_2».call h![] h![v])
      (fun r => ∃ st', r = some (st', Deposit.Main.f2 v)) := by
  apply Omni.consequence (Poseidon.Wrappers.wrapper2 s v Deposit.Main.f2 perm2t
    (Withdraw.Rules.mem1 Transfer.Lookup.x5_2_filter) (Withdraw.Rules.mem1 Transfer.Lookup.x5_2_config_filter) (Withdraw.Rules.mem1 Transfer.Lookup.config_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem x5_5_fwd (s : State p) (v : List.Vector (Fp p) 5) :
    Omni p Γt s («poseidon-0.0.0::poseidon::bn254::perm::x5_5».call h![] h![v])
      (fun r => ∃ st', r = some (st', Deposit.Main.f5 v)) := by
  apply Omni.consequence (Poseidon.Wrappers.wrapper5 s v Deposit.Main.f5 perm5t
    (Withdraw.Rules.mem1 Transfer.Lookup.x5_5_filter) (Withdraw.Rules.mem1 Transfer.Lookup.x5_5_config_filter) (Withdraw.Rules.mem1 Transfer.Lookup.config_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem x5_3_fwd (s : State p) (v : List.Vector (Fp p) 3) :
    Omni p Γt s («poseidon-0.0.0::poseidon::bn254::perm::x5_3».call h![] h![v])
      (fun r => ∃ st', r = some (st', Poseidon.Hash2.f3 v)) := by
  apply Omni.consequence (Poseidon.Hash2.wrapper3 s v Poseidon.Hash2.f3 perm3t
    (Withdraw.Rules.mem1 Transfer.Lookup.x5_3_filter) (Withdraw.Rules.mem1 Transfer.Lookup.x5_3_config_filter) (Withdraw.Rules.mem1 Transfer.Lookup.config_filter)
    (Withdraw.Rules.mem1 Transfer.Lookup.alpha_filter))
  rintro r ⟨s', h, _⟩
  exact ⟨s', h⟩

theorem hash_2_fwd (st : State p) (a b : Fp p) :
    Omni p Γt st («poseidon-0.0.0::poseidon::bn254::hash_2».call h![]
      h![(⟨[a,b],rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', Poseidon.Hash2.hash2v a b)) :=
  Poseidon.Hash2.hash2 a b Poseidon.Hash2.f3 (Withdraw.Rules.mem1 Transfer.Lookup.hash_2_filter) (Withdraw.Rules.mem1 Transfer.Lookup.hash_internal_filter) x5_3_fwd

theorem poseidon1_fwd (st : State p) (a : Fp p) :
    Omni p Γt st («transfer-0.0.0::poseidon1».call h![] h![a])
      (fun r => ∃ st', r = some (st', Deposit.Commitment.ownerKey a)) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.poseidon1_filter)
  dsimp only [«transfer-0.0.0::poseidon1»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((1 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact (Poseidon.Hash.hash1 a Deposit.Main.f2 (Withdraw.Rules.mem1 Transfer.Lookup.hash_1_filter)
      (Withdraw.Rules.mem1 Transfer.Lookup.hash_internal_filter) x5_2_fwd)

theorem poseidon4_fwd (st : State p) (a b c d : Fp p) :
    Omni p Γt st («transfer-0.0.0::poseidon4».call h![] h![a, b, c, d])
      (fun r => ∃ st', r = some (st', Deposit.Commitment.hash4 a b c d)) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.poseidon4_filter)
  dsimp only [«transfer-0.0.0::poseidon4»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((4 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact (Poseidon.Hash.hash4 a b c d Deposit.Main.f5 (Withdraw.Rules.mem1 Transfer.Lookup.hash_4_filter)
      (Withdraw.Rules.mem1 Transfer.Lookup.hash_internal_filter) x5_5_fwd)

theorem poseidon2_fwd (st : State p) (a b : Fp p) :
    Omni p Γt st («transfer-0.0.0::poseidon2».call h![] h![a, b])
      (fun r => ∃ st', r = some (st', Poseidon.Hash2.hash2v a b)) := by
  apply call _ _ _ (Withdraw.Rules.mem1 Transfer.Lookup.poseidon2_filter)
  dsimp only [«transfer-0.0.0::poseidon2»]
  repeat' first | atom | run_step | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ((2 : U 32),Tp.field)))
  all_goals try first | rfl | trivial
  all_goals exact hash_2_fwd _ a b
end

/-- Every derivation of the extracted transfer `poseidon1(a)` has an outcome with value `ownerKey a`. -/
theorem poseidon1_pinned {st Q} (a : Fp p)
    (h : Omni p Γt st («transfer-0.0.0::poseidon1».call h![] h![a]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.ownerKey a)) :=
  (tgood_poseidon1 Withdraw.Rules.bn254_gt a).pin (poseidon1_fwd st a) h

/-- Every derivation of the extracted transfer `poseidon4(a, b, c, d)` has an outcome with value
`hash4 a b c d`. -/
theorem poseidon4_pinned {st Q} (a b c d : Fp p)
    (h : Omni p Γt st («transfer-0.0.0::poseidon4».call h![] h![a, b, c, d]) Q) :
    ∃ st', Q (some (st', Deposit.Commitment.hash4 a b c d)) :=
  (tgood_poseidon4 Withdraw.Rules.bn254_gt a b c d).pin (poseidon4_fwd st a b c d) h

/-- Every derivation of the extracted transfer `poseidon2(a, b)` has an outcome with value
`hash2v a b`. -/
theorem poseidon2_pinned {st Q} (a b : Fp p)
    (h : Omni p Γt st («transfer-0.0.0::poseidon2».call h![] h![a, b]) Q) :
    ∃ st', Q (some (st', Poseidon.Hash2.hash2v a b)) :=
  (tgood_poseidon2 Withdraw.Rules.bn254_gt a b).pin (poseidon2_fwd st a b) h

#print axioms perm2t
#print axioms perm5t
#print axioms perm3t
#print axioms x5_2_fwd
#print axioms x5_5_fwd
#print axioms x5_3_fwd
#print axioms hash_2_fwd
#print axioms poseidon1_fwd
#print axioms poseidon4_fwd
#print axioms poseidon2_fwd
#print axioms poseidon1_pinned
#print axioms poseidon4_pinned
#print axioms poseidon2_pinned
end Transfer.Forward
