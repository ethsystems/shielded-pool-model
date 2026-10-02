# Approved theorem inventory
# Format (one per line, no leading spaces):
#   <fully.qualified.name> :: <pristine pp.all type, single line>
# The gate checks: each name exists, its pp.all type matches exactly,
# and its transitive axioms are within AXIOMS.md.
# L2 statement Props (re-frozen 2026-09-15 after the approved Fable fix,
# Oskar "accept" in controller pane; L2 human gate bd-14f closed 2026-09-15).
# The census checks these types only; statements/FROZEN.sha256 pins the bodies:
LeanShieldedPool.valueConservation :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noDoubleSpend :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.nullifierUniqueness :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.doubleSpendExhibitsCollision :: (P : LeanShieldedPool.PrimSpec) → Prop
# L4 Tier A statement Props (frozen 2026-09-15, Oskar's L4 go in pane):
LeanShieldedPool.poolSolvency :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noOverWithdrawal :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noMinting :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.balanceIsLiveValue :: (P : LeanShieldedPool.PrimSpec) → Prop
# L4 Tier B statement Props and theorems (promoted and frozen 2026-09-15):
LeanShieldedPool.spendRequiresOwnerKey :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.eventReplayFaithful :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.spendRequiresOwnerKey_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.spendRequiresOwnerKey P
LeanShieldedPool.eventReplayFaithful_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.eventReplayFaithful P
# L3 theorems (proofs of the frozen Props; landed 2026-09-15):
LeanShieldedPool.nullifierUniqueness_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.nullifierUniqueness P
LeanShieldedPool.noDoubleSpend_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noDoubleSpend P
LeanShieldedPool.valueConservation_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.valueConservation P
# L4 Tier A theorems (landed 2026-09-15):
LeanShieldedPool.poolSolvency_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.poolSolvency P
LeanShieldedPool.noOverWithdrawal_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noOverWithdrawal P
LeanShieldedPool.noMinting_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noMinting P
LeanShieldedPool.balanceIsLiveValue_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.balanceIsLiveValue P
