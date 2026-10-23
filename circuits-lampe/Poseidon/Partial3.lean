import Poseidon.Partial5
open Lampe

namespace Poseidon.Partial3
open Exec.Basic Exec.Heap
set_option backward.isDefEq.respectTransparency false
abbrev p := Crypto.Bn254.prime

def body (addr : Address) (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285) (r : U 8) : Expr (Tp.denote p) .unit :=
  («rounds::partial5».fn.body (Tp.denote p) h![(3 : U 32),(81 : U 32),(285 : U 32)]).body h![Ref.mk (.array .field 3) addr .nil,rc,sp,(3 : Fp p),(8 : U 8),(5 : Fp p),r]

def vec (a b c : Fp p) : List.Vector (Fp p) 3 := ⟨[a,b,c],rfl⟩
def get {n} (v : List.Vector (Fp p) n) (i : Nat) := v.toList[i]!
theorem get_eq {n} (v : List.Vector (Fp p) n) (i : Fin n) : v.get i = get v i.val := by
  simp [get, List.Vector.get_eq_get_toList, i.isLt]

def value (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285) (r : U 8) (a b c : Fp p) :=
  let a' := a^5 + get rc (15+r.toNat)
  vec (0 + get sp (5*r.toNat)*a' + get sp (5*r.toNat+1)*b + get sp (5*r.toNat+2)*c)
    (b + a'*get sp (5*r.toNat+3)) (c + a'*get sp (5*r.toNat+4))

theorem run {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285)
    (r : U 8) (hr : r.toNat < 57) (a b c : Fp p)
    (hv : st.vals.lookup addr = some ⟨.array .field 3,vec a b c⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (body addr rc sp r) (Cell st addr (tp := .array .field 3) (value rc sp r a b c)) := by
  unfold body
  dsimp only [«rounds::partial5»]
  atom
  apply bind_read hv
  atom
  apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 3) (vec a b c) 0 (by decide))
  apply bind_accept (Poseidon.Pow.pow_five a hpow hbits)
  intro st1 hk
  atom
  apply bind_modify (updated := vec (a^5) b c)
  · exact hk.2 _ _ hv
  · rfl
  have hr32 : (r.toNat : U 32).toNat = r.toNat := by
    change r.toNat%4294967296=r.toNat
    exact Nat.mod_eq_of_lt (by omega)
  have h25 : (15 : U 32).toNat + (r.toNat : U 32).toNat < 2^32 := by rw [hr32]; change 15+r.toNat < 4294967296; omega
  have hi25 : ((15 : U 32)+(r.toNat : U 32)).toNat < 81 := by
    rw [BitVec.toNat_add,hr32]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by change 15+r.toNat<81; omega)
  repeat' first
    | (apply bind_read; exact Finmap.lookup_insert _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 3) _ 0 (by decide))
    | apply bind_value (Exec.UIntOps.div (8 : U 8) 2 (by decide))
    | apply bind_value (Exec.UIntOps.add (4 : U 8) 1 (by decide))
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) 3 (by decide))
    | apply bind_value (Exec.UIntOps.add (15 : U 32) (r.toNat : U 32) h25)
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 81) rc _ hi25)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | atom
  let ap := a^5 + rc.get ⟨((15 : U 32)+(r.toNat : U 32)).toNat,hi25⟩
  apply bind_modify (updated := vec ap b c)
  · exact Finmap.lookup_insert _
  · rfl
  simp only [RefPath.modify, Finmap.insert_insert]
  apply bind_read
  · exact Finmap.lookup_insert _
  atom
  apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 3) (vec ap b c) 0 (by decide))
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
  have hmul : (5 : U 32).toNat*(r.toNat : U 32).toNat < 2^32 := by
    rw [hr32]; change 5*r.toNat<4294967296; omega
  have hmulnat : ((5 : U 32)*(r.toNat : U 32)).toNat = 5*r.toNat := by
    rw [BitVec.toNat_mul,hr32]
    exact Nat.mod_eq_of_lt (by change 5*r.toNat<4294967296; omega)
  have hadd (k : U 32) (hk : k.toNat ≤ 5) :
      ((5 : U 32)*(r.toNat : U 32)).toNat+k.toNat < 2^32 := by rw [hmulnat]; omega
  have hsp (k : U 32) (hk : k.toNat ≤ 4) :
      ((5 : U 32)*(r.toNat : U 32)+k).toNat < 285 := by
    rw [BitVec.toNat_add,hmulnat]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  have hsum5 : ((5 : U 32)*(r.toNat : U 32)+3).toNat = 5*r.toNat+3 := by
    rw [BitVec.toNat_add,hmulnat]
    exact Nat.mod_eq_of_lt (by change 5*r.toNat+3<4294967296; omega)
  have hlastadd (k : U 32) (hk : k.toNat ≤ 2) : ((5 : U 32)*(r.toNat : U 32)+3).toNat+k.toNat < 2^32 := by
    rw [hsum5]; omega
  have hlastsub (k : U 32) (hk : k.toNat ≤ 2) : (1 : U 32) ≤ (5 : U 32)*(r.toNat : U 32)+3+k := by
    change 1 ≤ ((5 : U 32)*(r.toNat : U 32)+3+k).toNat
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (hlastadd k hk),hsum5]
    omega
  have hlastnat (k : U 32) (hk : k.toNat ≤ 2) :
      ((5 : U 32)*(r.toNat : U 32)+3+k-1).toNat = 5*r.toNat+3+k.toNat-1 := by
    rw [BitVec.toNat_sub_of_le (hlastsub k hk),BitVec.toNat_add,Nat.mod_eq_of_lt (hlastadd k hk),hsum5]
    rfl
  have hlastidx (k : U 32) (hk : k.toNat ≤ 2) : ((5 : U 32)*(r.toNat : U 32)+3+k-1).toNat < 285 := by
    rw [hlastnat k hk]; omega
  repeat' ((try dsimp only [mapToValHeapCondition]); first
    | (apply bind_read; first
        | exact Finmap.lookup_insert _
        | (repeat' first | rw [Finmap.lookup_insert_of_ne _ hne.symm] | rw [Finmap.lookup_insert_of_ne _ hne]
           exact Finmap.lookup_insert _))
    | apply bind_value (Exec.ArrayOps.cast32 _)
    | apply bind_value (Exec.UIntOps.cast8_32 _)
    | apply bind_value (Exec.UIntOps.mul (3 : U 32) 2 (by decide))
    | apply bind_value (Exec.UIntOps.sub (6 : U 32) 1 (by decide))
    | apply bind_value (Exec.UIntOps.mul (5 : U 32) _ hmul)
    | (apply bind_value (Exec.UIntOps.add ((5 : U 32)*(r.toNat : U 32)) _ (hadd _ (by decide))))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 285) sp _ (hsp _ (by decide))))
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 3) _ _ (by decide)))
    | apply bind_value (Exec.ArrayOps.mul _ _)
    | apply bind_value (Exec.ArrayOps.add _ _)
    | apply bind_value (Exec.ArrayOps.sub _ _)
    | apply bind_value (Exec.UIntOps.castField32 _)
    | apply bind_value (Exec.UIntOps.add ((5 : U 32)*(r.toNat : U 32)+3) _ (hlastadd _ (by decide)))
    | apply bind_value (Exec.UIntOps.sub ((5 : U 32)*(r.toNat : U 32)+3+_) 1 (hlastsub _ (by decide)))
    | apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 285) sp _ (hlastidx _ (by decide)))
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
    | (apply bind_value (Exec.ArrayOps.index (tp := .field) (n := 3) _ _ (by decide)))
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
  all_goals change some (⟨Tp.array .field 3, vec (0 + sp.get ⟨((5 : U 32)*(r.toNat : U 32)+0).toNat,hsp 0 (by decide)⟩*ap + sp.get ⟨((5 : U 32)*(r.toNat : U 32)+1).toNat,hsp 1 (by decide)⟩*b + sp.get ⟨((5 : U 32)*(r.toNat : U 32)+2).toNat,hsp 2 (by decide)⟩*c)
    (b + ap*sp.get ⟨((5 : U 32)*(r.toNat : U 32)+3+1-1).toNat,hlastidx 1 (by decide)⟩)
    (c + ap*sp.get ⟨((5 : U 32)*(r.toNat : U 32)+3+2-1).toNat,hlastidx 2 (by decide)⟩)⟩ : (tp : Tp) × Tp.denote p tp) = _
  all_goals
    have hcn : ((15 : U 32)+(r.toNat : U 32)).toNat = 15+r.toNat := by
      rw [BitVec.toNat_add,hr32]
      exact Nat.mod_eq_of_lt (by change 15+r.toNat<4294967296; omega)
    have hsn (k : U 32) (hh : k.toNat ≤ 4) :
        ((5 : U 32)*(r.toNat : U 32)+k).toNat = 5*r.toNat+k.toNat := by
      rw [BitVec.toNat_add,hmulnat]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [ap, get_eq, hcn, hsn 0 (by decide), hsn 1 (by decide), hsn 2 (by decide),
      hlastnat 1 (by decide), hlastnat 2 (by decide)]
    try simp only [show 5*r.toNat+3+1-1 = 5*r.toNat+3 by omega,
      show 5*r.toNat+3+2-1 = 5*r.toNat+4 by omega]
    rfl

theorem vec_eta (v : List.Vector (Fp p) 3) : vec (v.get ⟨0,by decide⟩) (v.get ⟨1,by decide⟩) (v.get ⟨2,by decide⟩) = v := by
  apply List.Vector.ext
  intro i
  fin_cases i <;> rfl

def next (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285)
    (r : U 8) (v : List.Vector (Fp p) 3) :=
  value rc sp r (v.get ⟨0,by decide⟩) (v.get ⟨1,by decide⟩) (v.get ⟨2,by decide⟩)

def acc (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285)
    (v : List.Vector (Fp p) 3) : Nat → List.Vector (Fp p) 3
  | 0 => v
  | k+1 => next rc sp (k : U 8) (acc rc sp v k)

theorem run_vec {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285)
    (r : U 8) (hr : r.toNat < 57) (v : List.Vector (Fp p) 3)
    (hv : st.vals.lookup addr = some ⟨.array .field 3,v⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (body addr rc sp r) (Cell st addr (tp := .array .field 3) (next rc sp r v)) := by
  apply run st addr rc sp r hr _ _ _ _ hpow hbits
  simpa only [vec_eta] using hv

theorem loop {Γ} (st : State p) (addr : Address)
    (rc : List.Vector (Fp p) 81) (sp : List.Vector (Fp p) 285)
    (v : List.Vector (Fp p) 3)
    (hv : st.vals.lookup addr = some ⟨.array .field 3,v⟩)
    (hpow : «std-1.0.0-beta.21::field::pow_32» ∈ Γ.functions)
    (hbits : «std-1.0.0-beta.21::field::to_le_bits» ∈ Γ.functions) :
    Omni p Γ st (.loop (0 : U 8) (57 : U 8) (body addr rc sp))
      (Cell st addr (tp := .array .field 3) (acc rc sp v 57)) := by
  apply loop_cell (tp := .array .field 3) (0 : U 8) (57 : U 8) addr st
    (acc rc sp v) (body addr rc sp) (by decide) hv
  intro r s _ hr hval
  simpa only [acc, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    run_vec s addr rc sp r hr (acc rc sp v r.toNat) hval hpow hbits

#print axioms vec_eta
#print axioms run_vec
#print axioms loop

#print axioms get_eq
#print axioms run
end Poseidon.Partial3
