import Exec.Run
import Semantics.Bits
namespace Exec.BitWrapper
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

theorem modulus_len :
    (Builtin.arrayLenDesc (p := p) (.vector .bool) h![Builtin.modulusLeBitsDesc true h![] ]) =
      ⟨254 < 2^32, fun _ => (254 : U 32)⟩ := by
  rfl

theorem array_length32 {Γ st} (bits : List.Vector Bool 32) :
    Omni p Γ st (.callBuiltin [.array .bool 32] (.u 32) Builtin.arrayLen h![bits])
      (fun r => r = some (st, (32 : U 32))) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := Builtin.ArrayLenCase.array .bool 32) True.intro rfl

theorem modulus_length {Γ st} :
    Omni p Γ st (.callBuiltin [.vector .bool] (.u 32) Builtin.arrayLen
      h![Builtin.modulusLeBitsDesc true h![] ])
      (fun r => r = some (st, (254 : U 32))) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := Builtin.ArrayLenCase.vector .bool)
    (by change 254 < 2^32; decide) rfl

theorem five_bits_wrapper_state {Γ st}
    (hm : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st
      («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![(5 : Fp p)])
      (fun r => ∃ addr, addr ∉ st.vals ∧
        r = some (⟨st.vals.insert addr ⟨.bool, true⟩, st.lambdas⟩, Semantics.Bits.fiveBits)) := by
  apply call _ _ _ hm
  dsimp only [«std-1.0.0-beta.21::field::to_le_bits»]
  apply bind_value Semantics.Bits.five_run
  repeat' first
    | apply bind_value (array_length32 _)
    | apply bind_value modulus_length
    | apply bind_value Semantics.Bits.modulus_bool_run
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := true))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := Builtin.ArrayLenCase.array .bool 32))
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := Builtin.ArrayLenCase.vector .bool))
  all_goals try first | rfl | exact () | trivial
  all_goals try (simp only [modulus_len, Builtin.arrayLenDesc] at *)
  all_goals try first | trivial | decide +kernel
  all_goals try (dsimp [mapToValHeapCondition, RefPath.get]; exact ⟨_, by assumption, rfl⟩)
  all_goals trace_state
theorem five_bits_wrapper {Γ st}
    (hm : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st
      («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![(5 : Fp p)])
      (fun r => ∃ st', r = some (st', Semantics.Bits.fiveBits)) := by
  apply Omni.consequence (five_bits_wrapper_state hm)
  rintro _ ⟨addr, _, h⟩
  exact ⟨_, h⟩

#print axioms five_bits_wrapper_state
#print axioms array_length32
#print axioms modulus_length
#print axioms modulus_len
#print axioms five_bits_wrapper
end Exec.BitWrapper
