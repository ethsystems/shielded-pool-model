import Merkle.Fold

namespace Controls.Merkle
open Lampe Exec.Basic Exec.Heap Merkle.Fold
set_option backward.isDefEq.respectTransparency false

variable {p : Prime}

theorem bmr_fwd_direction_flipped {Γ : Env} (N : U 32) (h : Fp p → Fp p → Fp p) (hasher : FuncRef [.array .field 2] .field)
    (hmem : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ Γ.functions)
    (hfwd : ∀ st (a b : Fp p), Omni p Γ st (Expr.call [.array .field 2] .field hasher
      h![(⟨[a, b], rfl⟩ : List.Vector (Fp p) 2)]) (fun r => ∃ st', r = some (st', h a b)))
    (st : State p) (leaf : Fp p) (depth : U 32)
    (indices : List.Vector Bool N.toNat) (path : List.Vector (Fp p) N.toNat) :
    Omni p Γ st («binary_merkle_root-0.0.0::binary_merkle_root».call h![N]
        h![hasher, leaf, depth, indices, path])
      (fun r => ∃ st', r = some (st', merkleRoot (fun a b => h b a) leaf depth indices path)) := by
  apply call _ _ _ hmem
  dsimp only [«binary_merkle_root-0.0.0::binary_merkle_root»]
  apply bind_ref; intro addr hfresh
  exec_pure
  exec_pure
  apply Omni.letIn (Exec.Loop.loop_inv _ N _
    (fun i s => s.vals.lookup addr =
      some ⟨.field, (List.range i.toNat).foldl (level h depth.toNat indices.toList path.toList) leaf⟩)
    ?step (by simp [BitVec.le_def]) ?init)
  case init =>
    rw [Finmap.lookup_insert]; rfl
  case step =>
    intro i s hil hih hinv
    by_cases hd : i < depth
    · apply bind_value (ult_true hd)
      apply Omni.iteTrue
      apply bind_value (Exec.ArrayOps.cast32 i)
      apply bind_value (Exec.ArrayOps.index (tp := .field) (n := N) path i hih)
      apply bind_value (Exec.ArrayOps.cast32 i)
      apply bind_value (Exec.ArrayOps.index (tp := .bool) (n := N) indices i hih)
      generalize hb : indices.get ⟨i.toNat, hih⟩ = b
      apply bind_value (bnot_val b)
      cases b
      · -- indices[i] = false: the node is the left input
        refine bind_value (st' := s) (v := ?tv) ?h1 ?h2
        case h1 =>
          apply Omni.iteTrue
          apply bind_read hinv
          exact make_pair _ _
        case h2 =>
          apply bind_value (head_pair _ _)
          apply bind_value (tail_pair _ _)
          apply bind_value (mk_pair _ _)
          apply Omni.letIn (keep_lookup (fun st => hfwd st _ _) s addr _ hinv)
          · rintro _ _ ⟨s', heq, hl⟩
            cases heq
            apply Omni.letIn (Exec.Heap.write _ addr _ _ hl)
            · rintro _ _ ⟨s'', heq, hl', -⟩
              cases heq
              apply Omni.skip
              refine ⟨_, rfl, ?_⟩
              rw [hl', succ_toNat hih, fold_succ]
              simp only [level, show i.toNat < depth.toNat from hd, if_true,
                vget_getD indices _ hih, vget_getD path _ hih, hb, Bool.false_eq_true, if_false]
              rfl
            · rintro ⟨_, h, _⟩; cases h
          · rintro ⟨_, h, _⟩; cases h
      · -- indices[i] = true: the node is the right input
        refine bind_value (st' := s) (v := ?tvR) ?h1R ?h2R
        case h1R =>
          apply Omni.iteFalse
          apply bind_read hinv
          exact make_pair _ _
        case h2R =>
          apply bind_value (head_pair _ _)
          apply bind_value (tail_pair _ _)
          apply bind_value (mk_pair _ _)
          apply Omni.letIn (keep_lookup (fun st => hfwd st _ _) s addr _ hinv)
          · rintro _ _ ⟨s', heq, hl⟩
            cases heq
            apply Omni.letIn (Exec.Heap.write _ addr _ _ hl)
            · rintro _ _ ⟨s'', heq, hl', -⟩
              cases heq
              apply Omni.skip
              refine ⟨_, rfl, ?_⟩
              rw [hl', succ_toNat hih, fold_succ]
              simp only [level, show i.toNat < depth.toNat from hd, if_true,
                vget_getD indices _ hih, vget_getD path _ hih, hb, if_true]
              rfl
            · rintro ⟨_, h, _⟩; cases h
          · rintro ⟨_, h, _⟩; cases h
    · apply bind_value (ult_false hd)
      apply Omni.iteFalse
      apply Omni.skip
      refine ⟨s, rfl, ?_⟩
      rw [succ_toNat hih, fold_succ, hinv]
      simp only [level, show ¬ i.toNat < depth.toNat from hd, if_false]
  · rintro _ s' ⟨s'', heq, hinv⟩
    cases heq
    apply Omni.callBuiltin
    apply Builtin.readRefOmni.mk hinv
    exact ⟨_, rfl⟩
  · rintro ⟨_, h, _⟩; cases h

#print axioms bmr_fwd_direction_flipped
end Controls.Merkle
