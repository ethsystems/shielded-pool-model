import Poseidon.Pow
import Exec.UIntOps
open Lampe
noir_def rounds::partial2<T: u32, N: u32, X: u32>(state: & Array<Field, T: u32>, round_constants: Array<Field, N: u32>, sparse_mds: Array<Field, X: u32>, t: Field, rf: u8, alpha: Field, r: u8) -> Unit := {
    (state[(0: u32)]: Field) = («std-1.0.0-beta.21»::field::pow_32<> as λ(Field, Field) -> Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (0: u32)), alpha);
    (state[(0: u32)]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (0: u32)), (#_arrayIndex returning Field)(round_constants, (#_cast returning u32)((#_uAdd returning u32)((#_uMul returning u32)((#_cast returning u32)((#_uAdd returning u8)((#_uDiv returning u8)(rf, (2: u8)), (1: u8))), uConst!(T: u32)), (#_cast returning u32)(r)))));
    (#_asWitness returning Unit)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (0: u32)));
    {
      let newState0 = (#_ref returning & Field)((0: Field));
      for j in (0: u32) .. uConst!(T: u32) do {
        newState0 = (#_fAdd returning Field)((#_readRef returning Field)(newState0), (#_fMul returning Field)((#_arrayIndex returning Field)(sparse_mds, (#_cast returning u32)((#_uAdd returning u32)((#_uMul returning u32)((#_uSub returning u32)((#_uMul returning u32)(uConst!(T: u32), (2: u32)), (1: u32)), (#_cast returning u32)(r)), (#_cast returning u32)(j)))), (#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(j))));
        #_skip
      };
      for k in (1: u32) .. uConst!(T: u32) do {
        (state[k]: Field) = (#_fAdd returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(k)), (#_fMul returning Field)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (0: u32)), (#_arrayIndex returning Field)(sparse_mds, (#_cast returning u32)((#_uSub returning u32)((#_uAdd returning u32)((#_uAdd returning u32)((#_uMul returning u32)((#_cast returning u32)((#_fSub returning Field)((#_fMul returning Field)(t, (2: Field)), (1: Field))), (#_cast returning u32)(r)), uConst!(T: u32)), k), (1: u32))))));
        #_skip
      };
      (state[(0: u32)]: Field) = (#_readRef returning Field)(newState0);
      if (#_uEq returning bool)((#_uAnd returning u8)(r, (1: u8)), (0: u8)) then {
        for k in (1: u32) .. uConst!(T: u32) do {
          (#_asWitness returning Unit)((#_arrayIndex returning Field)((#_readRef returning Array<Field, T: u32>)(state), (#_cast returning u32)(k)));
          #_skip
        };
        #_skip
      }
    }
}

namespace Poseidon.Partial2
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def body (addr : Address) (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168) (r : U 8) : Expr (Tp.denote p) .unit :=
  («rounds::partial2».fn.body (Tp.denote p) h![(2 : U 32),(72 : U 32),(168 : U 32)]).body h![Ref.mk (.array .field 2) addr .nil,rc,sp,(2 : Fp p),(8 : U 8),(5 : Fp p),r]

def vec (a b : Fp p) : List.Vector (Fp p) 2 := ⟨[a,b],rfl⟩
def get {n} (v : List.Vector (Fp p) n) (i : Nat) := v.toList[i]!
theorem get_eq {n} (v : List.Vector (Fp p) n) (i : Fin n) : v.get i = get v i.val := by
  simp [get, List.Vector.get_eq_get_toList, i.isLt]

def value (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168) (r : U 8) (a b : Fp p) :=
  let a' := a^5 + get rc (10+r.toNat)
  vec (0 + get sp (3*r.toNat)*a' + get sp (3*r.toNat+1)*b)
    (b + a'*get sp (3*r.toNat+2))

theorem run {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168)
    (r : U 8) (hr : r.toNat < 56) (a b : Fp p)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,vec a b⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (body addr rc sp r) (Cell st addr (tp := .array .field 2) (value rc sp r a b)) := by
  unfold body
  dsimp only [«rounds::partial2»]
  atom
  apply bind_read hv
  atom
  apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) (vec a b) 0 (by decide))
  apply bind_accept (Poseidon.Pow.pow_five a hpow hbits)
  intro st1 hk
  atom
  apply bind_modify (updated := vec (a^5) b)
  · exact hk.2 _ _ hv
  · rfl
  have hr32 : (r.toNat : U 32).toNat = r.toNat := by
    change r.toNat%4294967296=r.toNat
    exact Nat.mod_eq_of_lt (by omega)
  have h10 : (10 : U 32).toNat + (r.toNat : U 32).toNat < 2^32 := by rw [hr32]; change 10+r.toNat < 4294967296; omega
  have hi10 : ((10 : U 32)+(r.toNat : U 32)).toNat < 72 := by
    rw [BitVec.toNat_add,hr32]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by change 10+r.toNat<72; omega)
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ 0 (by decide))
    | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (4 : U 8) 1 (by decide))
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (10 : U 32) (r.toNat : U 32) h10)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 72) rc _ hi10)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | atom
  let ap := a^5 + rc.get ⟨((10 : U 32)+(r.toNat : U 32)).toNat,hi10⟩
  apply bind_modify (updated := vec ap b)
  · exact Finmap.lookup_insert _
  · rfl
  simp only [RefPath.modify, Finmap.insert_insert]
  apply bind_read
  · exact Finmap.lookup_insert _
  atom
  apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) (vec ap b) 0 (by decide))
  apply bind_value (Exec.UIntOps.witness _)
  atom
  apply bind_ref
  intro aux haux
  have hne : aux ≠ addr := by
    intro heq; subst aux
    exact haux (Finmap.mem_insert.mpr (Or.inl rfl))
  have hn1 : aux ∉ st1.vals := by
    intro hh; exact haux (Finmap.mem_insert.mpr (Or.inr hh))
  have hn0 : aux ∉ st.vals := not_mem_of_keeps hk hn1
  have hmul : (3 : U 32).toNat*(r.toNat : U 32).toNat < 2^32 := by
    rw [hr32]; change 3*r.toNat<4294967296; omega
  have hmulnat : ((3 : U 32)*(r.toNat : U 32)).toNat = 3*r.toNat := by
    rw [BitVec.toNat_mul,hr32]
    exact Nat.mod_eq_of_lt (by change 3*r.toNat<4294967296; omega)
  have hadd (k : U 32) (hk : k.toNat ≤ 3) :
      ((3 : U 32)*(r.toNat : U 32)).toNat+k.toNat < 2^32 := by rw [hmulnat]; omega
  have hsp (k : U 32) (hk : k.toNat ≤ 2) :
      ((3 : U 32)*(r.toNat : U 32)+k).toNat < 168 := by
    rw [BitVec.toNat_add,hmulnat]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  have hsum2 : ((3 : U 32)*(r.toNat : U 32)+2).toNat = 3*r.toNat+2 := by
    rw [BitVec.toNat_add,hmulnat]
    exact Nat.mod_eq_of_lt (by change 3*r.toNat+2<4294967296; omega)
  have hlastadd : ((3 : U 32)*(r.toNat : U 32)+2).toNat+(1 : U 32).toNat < 2^32 := by
    rw [hsum2]; change 3*r.toNat+2+1<4294967296; omega
  have hlastsub : (1 : U 32) ≤ (3 : U 32)*(r.toNat : U 32)+2+1 := by
    change 1 ≤ ((3 : U 32)*(r.toNat : U 32)+2+1).toNat
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt hlastadd,hsum2]
    change 1 ≤ 3*r.toNat+2+1
    omega
  have hlastidx : ((3 : U 32)*(r.toNat : U 32)+2+1-1).toNat < 168 := by
    simpa only [BitVec.add_sub_cancel] using hsp 2 (by decide)
  repeat' ((try dsimp only [mapToValHeapCondition]); first
    | (apply bind_read; first
        | exact Finmap.lookup_insert _
        | (repeat' first | rw [Finmap.lookup_insert_of_ne _ hne.symm] | rw [Finmap.lookup_insert_of_ne _ hne]
           exact Finmap.lookup_insert _))
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.UIntOps.mul (2 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.sub (4 : U 32) 1 (by decide))
    | apply bind_value (Exec.UIntOps.mul (3 : U 32) _ hmul)
    | (apply bind_value (Exec.UIntOps.add ((3 : U 32)*(r.toNat : U 32)) _ (hadd _ (by decide))))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 168) sp _ (hsp _ (by decide))))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ _ (by decide)))
    | apply bind_value (Exec.ArrayOps.mul _ _)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.ArrayOps.sub _ _)
    | apply bind_value (Exec.UIntOps.castField32 _)
    | apply bind_value (Exec.UIntOps.add ((3 : U 32)*(r.toNat : U 32)+2) 1 hlastadd)
    | apply bind_value (Exec.UIntOps.sub ((3 : U 32)*(r.toNat : U 32)+2+1) 1 hlastsub)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 168) sp _ hlastidx)
    | apply bind_value (Exec.UIntOps.witness _)
    | apply bind_value (Exec.UIntOps.bitand _ _)
    | apply bind_value (Exec.UIntOps.eq _ _)
    | atom
    | apply bind_cps
    | (apply Omni.loopNext; · decide)
    | (apply Omni.loopDone; · decide)
    | (apply Omni.callBuiltin; apply Builtin.modifyLensOmni.ok (hr := rfl)
       · first | exact Finmap.lookup_insert _
               | (repeat' first | rw [Finmap.lookup_insert_of_ne _ hne.symm] | rw [Finmap.lookup_insert_of_ne _ hne]
                  exact Finmap.lookup_insert _)
       · rfl
       · rfl
       · rfl)
    | (apply Omni.callBuiltin; apply Builtin.readRefOmni.mk
       · first | exact Finmap.lookup_insert _
               | (repeat' first | rw [Finmap.lookup_insert_of_ne _ hne.symm] | rw [Finmap.lookup_insert_of_ne _ hne]
                  exact Finmap.lookup_insert _))
    | apply Omni.skip)
  change Omni p Γ _ (.ite (decide (r &&& 1 = 0)) _ _) _
  by_cases heven : r &&& 1 = 0
  all_goals try simp only [heven, decide_true, decide_false]
  all_goals first | apply Omni.iteTrue | apply Omni.iteFalse
  all_goals repeat' ((try dsimp only [mapToValHeapCondition]); first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 2) _ _ (by decide)))
    | apply bind_value (Exec.UIntOps.witness _)
    | atom
    | apply bind_cps
    | (apply Omni.loopNext; · decide)
    | (apply Omni.loopDone; · decide)
    | apply Omni.skip)
  all_goals dsimp only [Cell]
  all_goals refine ⟨_,rfl,?_,?_⟩
  all_goals try
    change Frame addr st _
    refine ⟨hk.1,?_⟩
    intro a val hmain hv
    have haaux : a ≠ aux := by
      intro h
      subst a
      exact hn0 (Finmap.mem_of_lookup_eq_some hv)
    simp only [Finmap.lookup_insert_of_ne _ hmain, Finmap.lookup_insert_of_ne _ haaux]
    exact hk.2 a val hv
  all_goals simp only [Finmap.lookup_insert, RefPath.get, RefPath.modify]
  all_goals change some (⟨Tp.array .field 2, vec
    (0 + sp.get ⟨((3 : U 32)*(r.toNat : U 32)+0).toNat,hsp 0 (by decide)⟩*ap +
      sp.get ⟨((3 : U 32)*(r.toNat : U 32)+1).toNat,hsp 1 (by decide)⟩*b)
    (b + ap*sp.get ⟨((3 : U 32)*(r.toNat : U 32)+2+1-1).toNat,hlastidx⟩)⟩ : (tp : Tp) × Tp.denote p tp) = _
  all_goals
    have hcn : ((10 : U 32)+(r.toNat : U 32)).toNat = 10+r.toNat := by
      rw [BitVec.toNat_add,hr32]
      exact Nat.mod_eq_of_lt (by change 10+r.toNat<4294967296; omega)
    have hsn (k : U 32) (hh : k.toNat ≤ 2) :
        ((3 : U 32)*(r.toNat : U 32)+k).toNat = 3*r.toNat+k.toNat := by
      rw [BitVec.toNat_add,hmulnat]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [ap, get_eq, hcn, BitVec.add_sub_cancel, hsn 0 (by decide), hsn 1 (by decide), hsn 2 (by decide)]
    rfl

theorem vec_eta (v : List.Vector (Fp p) 2) : vec (v.get ⟨0,by decide⟩) (v.get ⟨1,by decide⟩) = v := by
  apply List.Vector.ext
  intro i
  fin_cases i <;> rfl

def next (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168)
    (r : U 8) (v : List.Vector (Fp p) 2) :=
  value rc sp r (v.get ⟨0,by decide⟩) (v.get ⟨1,by decide⟩)

def acc (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168)
    (v : List.Vector (Fp p) 2) : Nat → List.Vector (Fp p) 2
  | 0 => v
  | k+1 => next rc sp (k : U 8) (acc rc sp v k)

theorem run_vec {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168)
    (r : U 8) (hr : r.toNat < 56) (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (body addr rc sp r) (Cell st addr (tp := .array .field 2) (next rc sp r v)) := by
  apply run st addr rc sp r hr _ _ _ hpow hbits
  simpa only [vec_eta] using hv

theorem loop {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 72) (sp : List.Vector (Fp p) 168)
    (v : List.Vector (Fp p) 2)
    (hv : st.vals.lookup addr = some ⟨.array .field 2,v⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (.loop (0 : U 8) (56 : U 8) (body addr rc sp))
      (Cell st addr (tp := .array .field 2) (acc rc sp v 56)) := by
  apply loop_cell (tp := .array .field 2) (0 : U 8) (56 : U 8) addr st
    (acc rc sp v) (body addr rc sp) (by decide) hv
  intro r s _ hr hval
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    run_vec s addr rc sp r hr (acc rc sp v r.toNat) hval hpow hbits

#print axioms vec_eta
#print axioms run_vec
#print axioms loop

#print axioms get_eq
#print axioms run
end Poseidon.Partial2
