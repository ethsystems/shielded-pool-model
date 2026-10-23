import Exec.UIntOps
namespace Poseidon.Config
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

theorem config2 {Γ st} (rc : List.Vector (Fp p) 72)
    (mds pre : List.Vector (List.Vector (Fp p) 2) 2) (sparse : List.Vector (Fp p) 168)
    (hm : «poseidon-0.0.0::poseidon::config» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::config».call h![(2 : U 32),(72 : U 32),(168 : U 32)]
      h![(2 : Fp p),(8 : U 8),(56 : U 8),(5 : Fp p),rc,mds,pre,sparse])
      (fun r => r = some (st,((2 : Fp p),(8 : U 8),(56 : U 8),(5 : Fp p),rc,mds,pre,sparse,()))) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::config»]
  repeat' first | run_step
  all_goals try first | rfl | trivial | decide +kernel
  all_goals try (norm_num [Builtin.CastTp.cast])
  all_goals try (change 2*8 < 256; decide)
  all_goals try (change 16+56 < 256; decide)
  all_goals try (change (72 : U 8) = 72; rfl)
  all_goals try (dsimp [mapToValHeapCondition]; apply Omni.callBuiltin)
  all_goals try (exact Builtin.genericPureOmni.ok (a := (some "«poseidon-0.0.0::poseidon::PoseidonConfig»", [Tp.field,.u 8,.u 8,.field,.array .field 72,.array (.array .field 2) 2,.array (.array .field 2) 2,.array .field 168])) True.intro rfl)

theorem config5 {Γ st} (rc : List.Vector (Fp p) 100)
    (mds pre : List.Vector (List.Vector (Fp p) 5) 5) (sparse : List.Vector (Fp p) 540)
    (hm : «poseidon-0.0.0::poseidon::config» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::config».call h![(5 : U 32),(100 : U 32),(540 : U 32)]
      h![(5 : Fp p),(8 : U 8),(60 : U 8),(5 : Fp p),rc,mds,pre,sparse])
      (fun r => r = some (st,((5 : Fp p),(8 : U 8),(60 : U 8),(5 : Fp p),rc,mds,pre,sparse,()))) := by
  apply call _ _ _ hm
  dsimp only [«poseidon-0.0.0::poseidon::config»]
  repeat' first | run_step
  all_goals try first | rfl | trivial | decide +kernel
  all_goals try (norm_num [Builtin.CastTp.cast])
  all_goals try (change 5*8 < 256; decide)
  all_goals try (change 40+60 < 256; decide)
  all_goals try (change (100 : U 8) = 100; rfl)
  all_goals try (dsimp [mapToValHeapCondition]; apply Omni.callBuiltin)
  all_goals try (exact Builtin.genericPureOmni.ok (a := (some "«poseidon-0.0.0::poseidon::PoseidonConfig»", [Tp.field,.u 8,.u 8,.field,.array .field 100,.array (.array .field 5) 5,.array (.array .field 5) 5,.array .field 540])) True.intro rfl)

#print axioms config5
#print axioms config2
end Poseidon.Config
