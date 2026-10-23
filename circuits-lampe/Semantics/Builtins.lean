import «std-1.0.0-beta.21».Extracted
import Lampe

namespace Semantics.Builtins
open Lampe

theorem let_value {p Γ st st' tp tp'} {e : Expr (Tp.denote p) tp}
    {b : Tp.denote p tp → Expr (Tp.denote p) tp'} {v Q}
    (he : Omni p Γ st e (fun r => r = some (st', v)))
    (hb : Omni p Γ st' (b v) Q) : Omni p Γ st (.letIn e b) Q := by
  apply Omni.letIn he
  · intro v' st'' h
    cases Option.some.inj h
    exact hb
  · intro h
    cases h

theorem diagnostic_succeeds {p Γ st} (template : NoirStr 121) (expected actual : U 32) :
    Omni p Γ st
      (.callBuiltin [.str 121, .u 32, .u 32] (.fmtStr 115 (.tuple none [.u 32, .u 32]))
        Builtin.mkFormatString h![template, expected, actual])
      (fun r => r = some (st, "")) := by
  apply Omni.callBuiltin
  apply Builtin.genericPureOmni.ok (a := ()) (h := True.intro)
  rfl

theorem diagnostic_keeps_false_assert_false {p st} (message : FormatString 115 (.tuple none [.u 32, .u 32])) :
    ¬ Builtin.staticAssert.omni p st [.bool, .fmtStr 115 (.tuple none [.u 32, .u 32])] .unit
      h![false, message] (fun r => r.isSome) := by
  intro h
  cases h with
  | ok h _ => cases h
  | err _ h => cases h

theorem unsupported_format_signature {p st Q} :
    ¬ Builtin.mkFormatString.omni p st [] .unit h![] Q := by
  intro h
  cases h

theorem asWitness_unsupported_signature {p st Q} :
    ¬ Builtin.asWitness.omni p st [] .unit h![] Q := by
  intro h
  cases h

theorem state_size_run {p Γ st}
    (hmem : «std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE» ∈ Γ.functions) :
    Omni p Γ st («std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE».call h![] h![])
      (fun r => r = some (st, (4 : U 32))) := by
  apply Omni.callDecl («fn» := «std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE».fn)
    (fnName := «std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE».name)
    rfl hmem rfl rfl rfl
  apply Omni.callBuiltin
  apply Builtin.genericPureOmni.ok (a := ()) (h := True.intro)
  rfl

theorem permutation_run {p Γ st} (input : List.Vector (Fp p) 4)
    (hconfig : «std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE» ∈ Γ.functions)
    (hperm : «std-1.0.0-beta.21::hash::poseidon2_permutation» ∈ Γ.functions) :
    Omni p Γ st
      («std-1.0.0-beta.21::hash::poseidon2_permutation».call h![(4 : U 32)] h![input])
      (fun r => r = some (st, Crypto.Poseidon2.noirPermutation4 input)) := by
  apply Omni.callDecl («fn» := «std-1.0.0-beta.21::hash::poseidon2_permutation».fn)
    (fnName := «std-1.0.0-beta.21::hash::poseidon2_permutation».name)
    rfl hperm rfl rfl rfl
  repeat' first
    | apply let_value
    | exact state_size_run hconfig
    | (apply Omni.fn; rfl)
    | (apply Omni.constU; rfl)
    | (apply Omni.litStr; rfl)
    | (apply Omni.var; rfl)
    | (apply Omni.callBuiltin
       apply Builtin.genericPureOmni.ok
       all_goals first | rfl | trivial | exact ())

theorem permutation_nonvacuous {p st} (input : List.Vector (Fp p) 4) :
    Omni p «std-1.0.0-beta.21».env st
      («std-1.0.0-beta.21::hash::poseidon2_permutation».call h![(4 : U 32)] h![input])
      (fun r => r = some (st, Crypto.Poseidon2.noirPermutation4 input)) := by
  apply permutation_run input
  · apply (show «std-1.0.0-beta.21».Hash.Mod.env ⊆ «std-1.0.0-beta.21».env from by solve_env_subset).1
    simp [«std-1.0.0-beta.21».Hash.Mod.env]
  · apply (show «std-1.0.0-beta.21».Hash.Mod.env ⊆ «std-1.0.0-beta.21».env from by solve_env_subset).1
    simp [«std-1.0.0-beta.21».Hash.Mod.env]

#print axioms unsupported_format_signature
#print axioms permutation_nonvacuous
#print axioms state_size_run
#print axioms permutation_run
#print axioms let_value
#print axioms diagnostic_succeeds
#print axioms diagnostic_keeps_false_assert_false
#print axioms asWitness_unsupported_signature
end Semantics.Builtins
