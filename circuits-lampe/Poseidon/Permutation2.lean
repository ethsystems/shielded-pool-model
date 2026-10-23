import Poseidon.Tail2
import Poseidon.Partial2
import Deposit.MainPermutations
namespace Poseidon.Permutation2
open Lampe Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def value (rc : List.Vector (Fp p) 72) (mds pre : List.Vector (List.Vector (Fp p) 2) 2)
    (sp : List.Vector (Fp p) 168) (v : List.Vector (Fp p) 2) :=
  let initial := Poseidon.Add2.initAcc rc 0 v 2
  let first := Poseidon.FullRound.acc 2 72 rc mds initial 3
  let middle := Poseidon.Matrix.outer pre (Poseidon.Add2.midAcc rc 0 (Poseidon.SigmaRound.acc first 2) 2) 2
  let partials := Poseidon.Partial2.acc rc sp middle 56
  let tail := Poseidon.Tail2.acc rc mds partials 3
  Poseidon.Matrix.outer mds (Poseidon.SigmaRound.acc tail 2) 2

theorem run {Γ} (st : State p) (rc : List.Vector (Fp p) 72)
    (mds pre : List.Vector (List.Vector (Fp p) 2) 2) (sp : List.Vector (Fp p) 168)
    (v : List.Vector (Fp p) 2)
    (hperm : «poseidon-0.0.0::poseidon::permute» ∈ Γ.functions)
    (hsigma : «poseidon-0.0.0::poseidon::sigma» ∈ Γ.functions)
    (hmatrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ Γ.functions)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st («poseidon-0.0.0::poseidon::permute».call h![(2 : U 32),(72 : U 32),(168 : U 32)]
      h![((2 : Fp p),(8 : U 8),(56 : U 8),(5 : Fp p),rc,mds,pre,sp,()),v])
      (Accept st (value rc mds pre sp v)) := by
  apply call _ _ _ hperm
  dsimp only [«poseidon-0.0.0::poseidon::permute»]
  apply bind_ref
  intro addr hfresh
  iterate 8 (apply bind_value; · apply Omni.callBuiltin; exact Builtin.genericPureOmni.ok (a := some «poseidon-0.0.0::poseidon::PoseidonConfig».name) True.intro rfl)
  atom
  apply bind_read (Finmap.lookup_insert _)
  apply bind_value (Exec.UIntOps.array_len 2 v)
  apply bind_cell (Poseidon.Add2.initLoop _ addr rc 0 (by decide) v (Finmap.lookup_insert _))
  intro s1 hv1 hf1
  repeat' first | atom | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide)) | apply bind_value (Exec.UIntOps.sub (4 : U 8) 1 (by decide))
  apply bind_cell (Poseidon.FullRound.loop 2 72 s1 addr rc mds _ Poseidon.AddRound.bounds2 hv1 hsigma hmatrix)
  intro s2 hv2 hf2
  atom
  apply bind_read hv2
  apply bind_accept (Poseidon.SigmaRound.sigma 2 _ hsigma)
  intro s3 hk3
  apply bind_cell (write s3 addr (tp := .array .field 2) _ _ (hk3.2 _ _ hv2))
  intro s4 hv4 hf4
  atom
  atom
  apply bind_cell (Poseidon.Add2.midLoop s4 addr rc 0 (by decide) _ hv4)
  intro s5 hv5 hf5
  atom
  apply bind_read hv5
  apply bind_accept (Poseidon.Matrix.matrix 2 pre _ hmatrix)
  intro s6 hk6
  apply bind_cell (write s6 addr (tp := .array .field 2) _ _ (hk6.2 _ _ hv5))
  intro s7 hv7 hf7
  atom
  atom
  apply bind_value (Poseidon.Add2.witnessLoop s7 addr _ hv7)
  atom
  apply bind_cell (Poseidon.Partial2.loop s7 addr rc sp _ hv7 hpow hbits)
  intro s8 hv8 hf8
  repeat' first | atom | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide)) | apply bind_value (Exec.UIntOps.sub (4 : U 8) 1 (by decide))
  apply bind_cell (Poseidon.Tail2.loop s8 addr rc mds _ hv8 hsigma hmatrix)
  intro s9 hv9 hf9
  atom
  apply bind_read hv9
  apply bind_accept (Poseidon.SigmaRound.sigma 2 _ hsigma)
  intro s10 hk10
  apply bind_cell (write s10 addr (tp := .array .field 2) _ _ (hk10.2 _ _ hv9))
  intro s11 hv11 hf11
  atom
  apply bind_read hv11
  apply bind_accept (Poseidon.Matrix.matrix 2 mds _ hmatrix)
  intro s12 hk12
  apply bind_cell (write s12 addr (tp := .array .field 2) _ _ (hk12.2 _ _ hv11))
  intro s13 hv13 hf13
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk hv13
  refine ⟨s13,rfl,?_⟩
  apply keeps_of_frame_fresh hfresh
  apply frame_trans (frame_of_keeps addr (keeps_fresh (tp := .array .field 2) st addr v hfresh))
  apply frame_trans hf1
  apply frame_trans hf2
  apply frame_trans (frame_of_keeps addr hk3)
  apply frame_trans hf4
  apply frame_trans hf5
  apply frame_trans (frame_of_keeps addr hk6)
  apply frame_trans hf7
  apply frame_trans hf8
  apply frame_trans hf9
  apply frame_trans (frame_of_keeps addr hk10)
  apply frame_trans hf11
  apply frame_trans (frame_of_keeps addr hk12)
  exact hf13

def f := value Poseidon.Constants2.rc Poseidon.Constants2.mds Poseidon.Constants2.pre Poseidon.Constants2.sparse

theorem perm : Poseidon.Wrappers.Perm2 Deposit.MainPermutations.Γ f := by
  intro st v
  exact run st _ _ _ _ v Deposit.Members.permute Deposit.Members.sigma Deposit.Members.matrix Deposit.Members.pow Deposit.Members.bits
#print axioms run
#print axioms perm
end Poseidon.Permutation2
