-- Control (must fail to compile): `RepCore` is `Rep` without the valid-roots field. The
-- window-inclusion proof of `Rep.known_root_in_window`, run verbatim on `RepCore`, does not
-- elaborate. The checked counterexample is `Toy.repCore_no_window_inclusion`.
import Refinement.Rep

open LeanShieldedPool LeanShieldedPool.Refine

theorem RepCore.known_root_in_window {P : PrimSpec} {H : Nat → Nat → Nat} {E : Enc P}
    {sup : P.Token → Prop} {L : List Nat} {σ : Storage} {st : St P}
    (hR : RepCore H E sup L σ st) {r : Nat}
    (hk : σ.isKnownRoot r) : ∃ n ∈ st.window, r = rootOf H (L.take n) := by
  rcases hk with hc | hv
  · refine ⟨L.length, List.mem_of_mem_head? hR.head, ?_⟩
    rw [hc, List.take_of_length_le (Nat.le_refl _)]
    exact congrArg Imt.root hR.tree
  · obtain ⟨hr0, p, hp, hpr⟩ := hR.valid r hv
    have hi := hR.ringIndex_lt
    have hj : (σ.ringIndex + 99 - (σ.ringIndex + 99 - p) % 100) % 100 = p := by omega
    have h1 := hR.ring ((σ.ringIndex + 99 - p) % 100) (Nat.mod_lt _ (by omega))
    unfold ringAt at h1
    rw [hj, hpr] at h1
    exact getD_windowRoots_ne_zero h1.symm hr0
