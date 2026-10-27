-- Control (must fail to compile): provenance `mono` along a non-prefix. Appending leaves keeps
-- old prefix roots; dropping leaves does not, so this has no proof by `mono`.
import Refinement.Provenance

namespace LeanShieldedPool.Refine

example {H : Nat → Nat → Nat} {L : List Nat} {c r : Nat} (h : PrefixRoot H (L ++ [c]) r) :
    PrefixRoot H L r :=
  h.mono (List.prefix_append L [c])

end LeanShieldedPool.Refine
