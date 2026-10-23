import Lampe
import Lampe.Crypto.Bn254.Prime

namespace Semantics.Bits
open Lampe
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def fiveBits : List.Vector Bool 32 := ⟨[true, false, true] ++ List.replicate 29 false, by decide⟩

theorem five_reconstructs :
    Builtin.toLeBitsDesc (p := p) .bool32 h![(5 : Fp p)] fiveBits := by
  rfl

theorem five_run {Γ st} :
    Omni p Γ st (.callBuiltin [.field] (.array .bool 32) Builtin.toLeBits h![(5 : Fp p)])
      (fun r => r = some (st, fiveBits)) := by
  apply Omni.callBuiltin
  exact Builtin.genericOmni.ok (a := Builtin.ToLeBitsSignature.bool32) five_reconstructs rfl

theorem supported_signature {A : Type} {sgn : A → List Tp × Tp} {desc p st argTps outTp args Q}
    (h : Builtin.genericOmni sgn desc p st argTps outTp args Q) :
    ∃ a, sgn a = (argTps, outTp) := by
  cases h <;> exact ⟨_, rfl⟩

theorem bool64_unsupported {p st Q} (x : Fp p) :
    ¬ Builtin.toLeBits.omni p st [.field] (.array .bool 64) h![x] Q := by
  intro h
  obtain ⟨a, ha⟩ := supported_signature h
  cases a <;> simp [Builtin.toLeBitsSgn] at ha

theorem wrong_bits_rejected :
    ¬ Builtin.toLeBitsDesc (p := p) .bool32 h![(5 : Fp p)]
      (List.Vector.replicate 32 false) := by
  change (5 : Fp p) ≠ 0
  decide

theorem legacy_run {p Γ st} (n : U 32) (x : Fp p)
    (bits : List.Vector (U 1) n.toNat)
    (h : x = RadixVec.ofDigitsLE (r := 2) (bits.map BitVec.toFin)) :
    Omni p Γ st (.callBuiltin [.field] (.array (.u 1) n) Builtin.toLeBits h![x])
      (fun r => r = some (st, bits)) := by
  apply Omni.callBuiltin
  exact Builtin.genericOmni.ok (a := Builtin.ToLeBitsSignature.legacy n) h rfl

theorem modulus_bool_run {p Γ st} :
    Omni p Γ st (.callBuiltin [] (.vector .bool) Builtin.modulusLeBits h![])
      (fun r => r = some (st, (RadixVec.toDigitsLE' 2 p.natVal).map (fun b => b.val == 1))) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := true) True.intro rfl

theorem modulus_legacy_run {p Γ st} :
    Omni p Γ st (.callBuiltin [] (.vector (.u 1)) Builtin.modulusLeBits h![])
      (fun r => r = some (st, (RadixVec.toDigitsLE' 2 p.natVal).map BitVec.ofFin)) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := false) True.intro rfl

#print axioms supported_signature
#print axioms legacy_run
#print axioms five_reconstructs
#print axioms five_run
#print axioms bool64_unsupported
#print axioms wrong_bits_rejected
#print axioms modulus_bool_run
#print axioms modulus_legacy_run
#print axioms Builtin.toLeBits
#print axioms Builtin.modulusLeBits
end Semantics.Bits
