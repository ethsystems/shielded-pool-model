import Exec.Heap
open Lampe
noir_def steps::pow_step<>(r: & Field, b: Array<bool, 32: u32>, self: Field, i: u32) -> Unit := {
  r = (#_fMul returning Field)((#_readRef returning Field)(r), (#_readRef returning Field)(r));
  r = (#_fAdd returning Field)((#_fMul returning Field)((#_cast returning Field)((#_arrayIndex returning bool)(b, (#_cast returning u32)((#_uSub returning u32)((32: u32), i)))), (#_fMul returning Field)((#_readRef returning Field)(r), self)), (#_fMul returning Field)((#_fSub returning Field)((1: Field), (#_cast returning Field)((#_arrayIndex returning bool)(b, (#_cast returning u32)((#_uSub returning u32)((32: u32), i))))), (#_readRef returning Field)(r)));
  #_skip
}
namespace Poseidon.Pow
open Exec.Basic
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def put (st : State p) (addr : Address) (v : Fp p) : State p :=
  ⟨st.vals.insert addr ⟨.field, v⟩, st.lambdas⟩

def body (addr : Address) (bits : List.Vector Bool 32) (x : Fp p) (i : U 32) :=
  («steps::pow_step».fn.body (Tp.denote p) h![]).body h![Ref.mk .field addr .nil, bits, x, i]

def next (x v : Fp p) (bit : Bool) : Fp p :=
  (if bit then 1 else 0) * ((v*v)*x) + (1-(if bit then 1 else 0)) * (v*v)

theorem step {Γ} (st : State p) (addr : Address) (bits : List.Vector Bool 32)
    (x v : Fp p) (i : U 32) (hlo : 1 ≤ i.toNat) (hhi : i.toNat < 33) :
    Omni p Γ (put st addr v) (body addr bits x i)
      (fun r => r = some (put st addr (next x v (bits.get ⟨32-i.toNat, by omega⟩)), ())) := by
  have hidx : (32-i).toNat < 32 := by
    change (4294967296-i.toNat+32)%4294967296 < 32
    omega
  have hval : (32-i).toNat = 32-i.toNat := by
    change (4294967296-i.toNat+32)%4294967296 = 32-i.toNat
    omega
  unfold body
  dsimp only [«steps::pow_step»]
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | run_step
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := (Tp.bool, (32 : U 32))))
  all_goals try first
    | rfl | trivial
    | (change i.toNat ≤ 32; omega)
    | (change (32-i).toNat < 32; exact hidx)
  change some (put (put (put st addr v) addr (v*v)) addr
    (next x v (bits.get ⟨(32-i).toNat,hidx⟩)), ()) = _
  have heq : (⟨(32-i).toNat, hidx⟩ : Fin 32) = ⟨32-i.toNat, by omega⟩ := Fin.ext hval
  rw [heq]
  simp only [put, Finmap.insert_insert]
def acc (x : Fp p) : Nat → Fp p
  | 0 => 1
  | n+1 => next x (acc x n) (Semantics.Bits.fiveBits.toList[32-(n+1)]!)

theorem acc_step (x : Fp p) (i : Nat) (hlo : 1 ≤ i) (hhi : i < 33) :
    next x (acc x (i-1)) (Semantics.Bits.fiveBits.get ⟨32-i, by omega⟩) = acc x i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Nat.add_sub_cancel, acc]
  congr 1
  have hb : 31-n < Semantics.Bits.fiveBits.toList.length := by simp; omega
  simp [List.Vector.get_eq_get_toList, List.getElem?_eq_getElem hb]

theorem acc_final (x : Fp p) : acc x 32 = x^5 := by
  norm_num [acc, next, Semantics.Bits.fiveBits, List.Vector.toList]
  ring

theorem loop {Γ} (st : State p) (addr : Address) (x : Fp p) :
    Omni p Γ (put st addr 1) (.loop (1 : U 32) (33 : U 32) (body addr Semantics.Bits.fiveBits x))
      (fun r => r = some (put st addr (x^5), ())) := by
  refine Omni.consequence (Exec.Loop.loop_inv (1 : U 32) (33 : U 32)
    (body addr Semantics.Bits.fiveBits x)
    (fun i s => s = put st addr (acc x (i.toNat-1))) ?_ (by decide) (by rfl)) ?_
  · intro i s hlo hhi hs
    subst s
    have hi1 : 1 ≤ i.toNat := hlo
    have hi33 : i.toNat < 33 := hhi
    apply Omni.consequence (step st addr Semantics.Bits.fiveBits x (acc x (i.toNat-1)) i hi1 hi33)
    intro r hr
    refine ⟨_, hr, ?_⟩
    have hv : (i+1).toNat = i.toNat+1 := by
      change (i.toNat+1)%4294967296 = i.toNat+1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hv, Nat.add_sub_cancel, acc_step x i.toNat hi1 hi33]
  · rintro r ⟨s, hr, hs⟩
    change s = put st addr (acc x 32) at hs
    rw [acc_final] at hs
    simpa [hs] using hr

theorem bind_bits {Γ st tp} {b : List.Vector Bool 32 → Expr (Tp.denote p) tp} {Q}
    (hm : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions)
    (next : ∀ addr, addr ∉ st.vals →
      Omni p Γ ⟨st.vals.insert addr ⟨.bool, true⟩, st.lambdas⟩ (b Semantics.Bits.fiveBits) Q) :
    Omni p Γ st (.letIn
      («std-1.0.0-beta.21::field::to_le_bits».call h![(32 : U 32)] h![(5 : Fp p)]) b) Q := by
  apply Omni.letIn (Exec.BitWrapper.five_bits_wrapper_state hm)
  · rintro _ _ ⟨addr, hfresh, h⟩
    cases Option.some.inj h
    exact next addr hfresh
  · rintro ⟨_, _, h⟩; cases h

def withBit (st : State p) (addr : Address) : State p :=
  ⟨st.vals.insert addr ⟨.bool, true⟩, st.lambdas⟩

theorem pow_five_state {Γ st} (x : Fp p)
    (hm : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st («std-1.0.0-beta.21::field::pow_32».call h![] h![x, (5 : Fp p)])
      (fun r => ∃ addr bitsaddr, addr ∉ st.vals ∧ bitsaddr ∉ st.vals ∧ addr ≠ bitsaddr ∧
        r = some (put (withBit st bitsaddr) addr (x^5), x^5)) := by
  apply call _ _ _ hm
  dsimp only [«std-1.0.0-beta.21::field::pow_32»]
  exec_pure
  apply bind_ref
  intro addr hfresh
  exec_pure
  apply bind_bits hbits
  intro bitsaddr bitsfresh
  have hne : addr ≠ bitsaddr := by
    intro heq; subst bitsaddr
    exact bitsfresh (Finmap.mem_insert.mpr (Or.inl rfl))
  have hb : bitsaddr ∉ st.vals := by
    intro hb; exact bitsfresh (Finmap.mem_insert.mpr (Or.inr hb))
  rw [Finmap.insert_insert_of_ne _ hne]
  exec_pure
  exec_pure
  apply bind_value (loop (withBit st bitsaddr) addr x)
  apply Omni.callBuiltin
  apply Builtin.readRefOmni.mk
  · exact Finmap.lookup_insert _
  exact ⟨addr, bitsaddr, hfresh, hb, hne, rfl⟩

theorem pow_five {Γ st} (x : Fp p)
    (hm : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st («std-1.0.0-beta.21::field::pow_32».call h![] h![x, (5 : Fp p)])
      (Exec.Heap.Accept st (tp := .field) (x^5)) := by
  refine Omni.consequence (pow_five_state x hm hbits) ?_
  rintro r ⟨a,b,ha,hb,hab,hr⟩
  refine ⟨_, hr, Exec.Heap.keeps_trans (Exec.Heap.keeps_fresh st b (tp := .bool) true hb) ?_⟩
  apply Exec.Heap.keeps_fresh (tp := .field)
  simpa only [Exec.Heap.set, Finmap.mem_insert, not_or] using And.intro hab ha

#print axioms pow_five
#print axioms bind_bits
#print axioms pow_five_state
#print axioms step
#print axioms acc_step
#print axioms acc_final
#print axioms loop
end Poseidon.Pow
