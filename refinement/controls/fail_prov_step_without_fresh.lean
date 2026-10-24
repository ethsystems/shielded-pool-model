-- Control (must fail to compile): `prov_step` with the freshness premise replaced by "every true
-- key was true before", which a call that records a root does not satisfy. The proof term from
-- the old flags cannot type-check, so the valid-roots premise is used.
import Refinement.Provenance

namespace LeanShieldedPool.Refine

example {H : Nat → Nat → Nat} {L : List Nat} (c : Nat) (σ : Storage) (hP : Prov H L σ) :
    Prov H (L ++ [c]) (depositStorage H σ c) :=
  prov_step (M := [c]) hP rfl (fun r hr => Or.inl hr)

end LeanShieldedPool.Refine
