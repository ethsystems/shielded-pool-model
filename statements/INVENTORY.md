# Approved theorem inventory
# Format (one per line, no leading spaces):
#   <fully.qualified.name> :: <pristine pp.all type, single line>
# The gate checks: each name exists, its pp.all type matches exactly,
# and its transitive axioms are within AXIOMS.md.
# L3 statement Props. The census checks the types of all Props below;
# statements/FROZEN.sha256 pins their bodies:
LeanShieldedPool.valueConservation :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noDoubleSpend :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.nullifierUniqueness :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.doubleSpendExhibitsCollision :: (P : LeanShieldedPool.PrimSpec) → Prop
# L4 statement Props:
LeanShieldedPool.poolSolvency :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noOverWithdrawal :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.noMinting :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.balanceIsLiveValue :: (P : LeanShieldedPool.PrimSpec) → Prop
# L4B statement Props and theorems:
LeanShieldedPool.spendRequiresOwnerKey :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.eventReplayFaithful :: (P : LeanShieldedPool.PrimSpec) → Prop
LeanShieldedPool.spendRequiresOwnerKey_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.spendRequiresOwnerKey P
LeanShieldedPool.eventReplayFaithful_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.eventReplayFaithful P
# L3 theorems:
LeanShieldedPool.nullifierUniqueness_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.nullifierUniqueness P
LeanShieldedPool.noDoubleSpend_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noDoubleSpend P
LeanShieldedPool.valueConservation_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.valueConservation P
# L4 theorems:
LeanShieldedPool.poolSolvency_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.poolSolvency P
LeanShieldedPool.noOverWithdrawal_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noOverWithdrawal P
LeanShieldedPool.noMinting_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.noMinting P
LeanShieldedPool.balanceIsLiveValue_proof :: ∀ (P : LeanShieldedPool.PrimSpec), LeanShieldedPool.balanceIsLiveValue P
# L5 epoch statement Props (semantic model of the PoC extension spec):
LeanShieldedPool.Epoch.Tx.valueConsumes :: {P : LeanShieldedPool.Epoch.PrimSpec} → LeanShieldedPool.Epoch.Tx P → List.{0} (LeanShieldedPool.PrimSpec.Commitment (LeanShieldedPool.Epoch.PrimSpec.toPrimSpec P))
LeanShieldedPool.Epoch.Candidates.BallastStamped :: {P : LeanShieldedPool.Epoch.PrimSpec} → (txs : List.{0} (LeanShieldedPool.Epoch.Tx P)) → Prop
LeanShieldedPool.Epoch.Candidates.crossEpochNoDoubleSpend :: (P : LeanShieldedPool.Epoch.PrimSpec) → Prop
LeanShieldedPool.Epoch.Candidates.frozenRootImmutability :: (P : LeanShieldedPool.Epoch.PrimSpec) → Prop
LeanShieldedPool.Epoch.Candidates.canonicalAppend :: (P : LeanShieldedPool.Epoch.PrimSpec) → Prop
LeanShieldedPool.Epoch.Candidates.chainKeyBinding :: (P : LeanShieldedPool.Epoch.PrimSpec) → Prop
LeanShieldedPool.Epoch.Candidates.epochZeroRefinesBase :: (P : LeanShieldedPool.Epoch.PrimSpec) → Prop
# L5 epoch theorems:
LeanShieldedPool.Epoch.crossEpochNoDoubleSpend_proof :: ∀ (P : LeanShieldedPool.Epoch.PrimSpec), LeanShieldedPool.Epoch.Candidates.crossEpochNoDoubleSpend P
LeanShieldedPool.Epoch.frozenRootImmutability_proof :: ∀ (P : LeanShieldedPool.Epoch.PrimSpec), LeanShieldedPool.Epoch.Candidates.frozenRootImmutability P
LeanShieldedPool.Epoch.canonicalAppend_proof :: ∀ (P : LeanShieldedPool.Epoch.PrimSpec), LeanShieldedPool.Epoch.Candidates.canonicalAppend P
LeanShieldedPool.Epoch.chainKeyBinding_proof :: ∀ (P : LeanShieldedPool.Epoch.PrimSpec), LeanShieldedPool.Epoch.Candidates.chainKeyBinding P
LeanShieldedPool.Epoch.epochZeroRefinesBase_proof :: ∀ (P : LeanShieldedPool.Epoch.PrimSpec), LeanShieldedPool.Epoch.Candidates.epochZeroRefinesBase P
