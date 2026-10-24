# refinement: a conditional refinement of the pool contract to the gated model

This package proves, in Lean, how the contract-level facts about the shielded pool compose into
the gated model of the parent directory. It states an abstract model of the pool contract's
storage and calls (`Refinement/Storage.lean`), names every fact about the contract, the circuits,
the Merkle tree and the tokens as a premise, and proves that under those premises every accepted
history of the pinned deployment refines a run of the model, so the model's money theorems apply
to it. It also proves the tree results the composition needs (the LeanIMT tree against the
circuit's Merkle fold, and a bridge from the circuit's field fold), a token-balance bound for
withdrawals, one withdrawal composed across all the hops, and the arithmetic of a gas argument.

The package requires the parent package by path (`lakefile.toml`, `path = ".."`). Its theorems
are about the gated model at this commit, unchanged: the model modules it imports are those of
`../LeanShieldedPool/`, and `PINS.sha256` pins their hashes. It is separate from the gate: it has
its own lakefile and check, the same toolchain (Lean 4.33.1, Mathlib at the parent's pin), and
the gate does not build it. Nothing here changes the claim of the parent README.

Every result is conditional. No premise is discharged here for the deployed pool; the composition
is a theorem about what the premises imply, not about what the deployment does.

## The claim

For every abstract contract `X` (an uninterpreted success relation `X.Exec`, revert relation
`X.Fail` and verifier relation `X.Verified`), every hash `H : Nat → Nat → Nat` (free: the
theorems hold for every function), every accepted history `h` of `X` with no successful
`setVerifier` call, and every witness extractor `ext`: if the contract, circuit, tree and
cryptographic premises below hold, then the extracted operations of `h` (up to the model's root
snapshot) form a run of the gated model from the empty pool, whose state the storage represents,
and the model's money theorems (no double spend, value conservation, solvency, no
over-withdrawal, no minting, balance equals live value, owner-key binding) hold for that run.
With the token premises, the pool's external token balance bounds the model's balance and every
amount the model's withdrawal guard admits. Machine-checked with the three standard Lean axioms
only (`propext`, `Classical.choice`, `Quot.sound`); no proof uses `native_decide`.

## The results

All declarations of the main package are in the namespace `LeanShieldedPool.Refine` (the gas
arithmetic in `GasEnvelope`); the fold bridge is in `FoldBridge`.
[statements/INVENTORY.md](statements/INVENTORY.md) lists the 474 theorems of the main package
and [statements/FOLD-BRIDGE.md](statements/FOLD-BRIDGE.md) those of the fold bridge, each with
its exact statement.

### Root provenance (`Refinement/Provenance.lean`)

- `accepted_root_provenance`: from `ConstructorPost X`, `Rollback X`, `ValidRootsFresh X` and
  `TreeAppend H X`, for every accepted history `h` with `NoSetVerifier h`, every root `r` that
  the storage accepts (`isKnownRoot`: the current root, or a `validRoots` flag that is true) is
  the LeanIMT root `rootOf H (L.take n)` of a prefix of the history's leaves `L = ghostLeaves h`.
- `transfer_root_provenance`, `withdraw_root_provenance`: with `TransferPost` or `WithdrawPost`
  in addition, the root of every successful transfer or withdrawal from an accepted state is
  such a prefix root.
- `prov_run_of_posts`: the two provenance premises follow from the contract posts
  (`validRootsFresh_of_posts`, `treeAppend_of_posts`), so provenance holds under the premise set
  of the refinement, with no nonzero-root premise and no ring premise.
- `Step'` (`Refinement/ProvenanceModel.lean`) is the model's `Step` with the root conjunct of the
  transfer and withdraw guards replaced by provenance (`snapshot ≤ minted.length`; every other
  conjunct and every post-state unchanged, `transfer_guard_iff`, `withdraw_guard_iff`).
  `Run'.to_run` maps every `Step'` run to a `Step` run with the same states and the same
  operations up to snapshots, so the money theorems hold for `Step'` runs (`*_prov`).

### The refinement (`Refinement/Cases.lean`, `Refinement/ProvenanceRefine.lean`)

- `refineP_run`: premises `ConstructorPost X`, `Rollback X`, `OwnerCallbackFree X`,
  `DepositPost H X`, `TransferPost H X`, `WithdrawPost X`, `AdminStutter X`,
  `CircuitFacts E C Incl`, `Function.Injective E.cm`; for the history: `Accepted X h σ`,
  `NoSetVerifier h`, `ExtractedWitnesses C ext h`, `TreeLink H Incl Coll (ghostLeaves h)
  (inputWords E ext h)`, `TreeHyp Coll (ghostLeaves h) (inputWords E ext h)` and
  `CryptoHyp P (txsOf ext h)`. Conclusion: there are `txs` and `st` with
  `txs.map eraseSnap = txsOf ext h`, `Run' (supOf E h) txs st` and
  `RepP H E (supOf E h) (ghostLeaves h) σ st`. `refineP_valueConservation` gives value
  conservation for that run.
- `refine_run`: the same premises plus `RootsNonzero H h` (every recorded root is nonzero), with
  the conclusion in the model's own `Run` and the representation `Rep` (ring and window fields
  included). `refineP_run` drops that premise and moves to `Step'`.
- The cases: `deposit_step`, `transfer_step`, `withdraw_step` and `stutter_inv` for the owner
  calls (and the `P` forms); `withdraw_balance` shows from the model alone that a withdrawable note is covered by
  the pool balance (row W9 is redundant in the model).

### Path-local tree premises (`Refinement/PathLocal.lean`)

- `refinePL_run`: the premises of `refineP_run` with `TreeLink` and `TreeHyp` replaced by
  `PathFacts H E C ext pext` and `PathTreeHyp H (ghostLeaves h) (checkedInputs E ext pext h)`;
  the conclusion is unchanged. `pext : PathExt` is the path part of the extracted witness.
- The membership-checked inputs (`Call.checked`): input 0 of every transfer (zero amount
  included), input 1 only when its amount is nonzero, and the note of every withdrawal. A
  ballast input 1 carries no obligation.

### The LeanIMT tree and the circuit fold (`Tree/LeanImt.lean`, `Tree/Checks.lean`)

For an abstract hash `H`, in namespace `LeanImt`:

- `rootOf_eq_sub`: the contract model `imtInsert` (a transcription of `InternalLeanIMT._insert`,
  zk-kit.solidity, read by hand) computes the LeanIMT specification `sub H depth L` for every leaf
  list inserted from the empty tree.
- `merkleRoot` is the circuit fold `Merkle.Fold.merkleRoot` of `circuits-lampe/` over `Nat`.
  `complete_mem`: for a tree of at most `2^32` leaves, every leaf has a compressed proof of length
  at most 32 that folds it to `rootOf H L`.
- `binding_mem_or_bad`: if `leaf ≠ 0` and `merkleRoot H leaf d I P = rootOf H L`, then
  `leaf ∈ L` or `Bad H (imtOf H L).depth L leaf (activePath d I P n)`. `Bad` is a hash collision
  between a fold input pair and a tree node's children pair, a leaf equal to an internal node, or
  a fold output equal to a leaf (or to 0 in the empty tree).
- `treeLink`: the refinement's `TreeLink` holds for the real fold at every depth, for every hash,
  with `Incl := InclC H` and `Coll := CollC H`.
- Checks: a three-leaf tree (`three_*`), each structural bad case occurs (`collision_occurs`,
  `nodeAsLeaf_occurs`, `leafAsNode_occurs`), and fold-direction and insertion mutants break the
  results (`control_flip_breaks_complete`, `control_left_breaks_complete`,
  `control_swap_insert`, `control_zero_pad`).

### The fold bridge (`fold-bridge/`)

The bridge is compiled in the Lean workspace of `../circuits-lampe` (Lampe at its pinned fork and
the extracted circuits), with the model and tree modules it imports compiled again from their
unchanged sources. In namespace `FoldBridge`, with `Hn h a b = (h (a : Fp p) (b : Fp p)).val`:

- `merkleRoot_val`: for every prime, hash `h`, width, leaf, `U 32` depth, direction bits and path,
  the value of the circuit's field fold `Merkle.Fold.merkleRoot h leaf depth indices path` is the
  LeanIMT fold `LeanImt.merkleRoot (Hn h) leaf.val depth.toNat indices (path.map (·.val))`.
- `complete_field`, `binding_mem_or_bad_field`, `binding_eq`, `inclC_of_field`: completeness and
  binding of the LeanIMT module restated for the field fold.
- `bad_field`: when every leaf of `L` is below the field modulus (the Solidity `_insert` range
  check), `LeanImt.Bad` on a field path is a field-level bad event (`BadF`): a collision of two
  distinct pairs of field elements, or a structural case, never two words equal modulo `p`.
- `withdraw_member_or_bad`: in every accepting execution of the complete extracted withdraw
  `main` whose public `commitment_root` has the contract root `rootOf (Hn hash2v) L` as its value,
  the note commitment, if nonzero, is a leaf of `L`, or `LeanImt.Bad` holds on the witness path.
  `transfer_member_or_bad`: the same for transfer input 0, and for input 1 when
  `amount_in_1 ≠ 0`. Both use `Withdraw.Root.accepting_main_withdraw_root` and
  `Transfer.Root.accepting_main_transfer_root` of `circuits-lampe/`.
- Non-vacuity: `withdraw_tree_nonvacuous` (for every tree of at most `2^32` leaves that contains
  the zero note, the withdraw `main` has an accepting execution with the contract root as its
  public root, at the depth of the compressed proof) and `transfer_tree_nonvacuous` (depth 0).

### Token balances (`Balance/`)

The pool's external balances enter as a parameter `K : Chain` (`K.bal w tok a` is
`IERC20(tok).balanceOf(a)` in chain state `w`; the chain's step relations are uninterpreted).
`Ext.credit` and `Ext.debit` compute the credit and debit a token call states from its arguments:
accounting definitions, not token behaviour. `AcceptedB X K h σ w` is an accepted history with the
chain state beside the storage (outside transactions move the chain only).

- `ledger_le_bal`: from `TokenCallFacts X`, `NoOutsideDebit X K`, `TokenRollback X K`,
  `AcceptedB X K h σ w` and `NoSetVerifier h`, the calldata ledger (deposits minus withdrawals of
  each token, `ledger h t`) is at most the pool's balance `K.bal w t X.self`.
- `bal_eq_ledger`: with `PoolStartsEmpty X K`, `NoOutsideCredit X K` and `NoSelfWithdraw X h`
  in addition, they are equal.
- `refineB_w9`: the premises of `refineP_run` with `AcceptedB X K h σ w` in place of
  `Accepted X h σ`, plus `Function.Injective E.tok`, `PoolCallReadings X`, `NoOutsideDebit X K`
  and `TokenRollback X K`:
  the conclusion of `refineP_run`, and the model's balance and live value of every token are at
  most the external balance, and so is the amount of every withdrawal the model's guard admits.
- `refineB_run`: with `PoolStartsEmpty`, `NoOutsideCredit` and `NoSelfWithdraw` in addition, the
  external balance equals the model's balance and the live value.
- `refineBPL_w9`, `refineBPL_run` (`Balance/PathLocal.lean`): the same on the path-local premises.
- `withdraw_debits_pool`, `withdraw_credits_recipient`, `deposit_credits_pool`: the stated deltas
  of each call kind. No recipient balance and no single transfer is established.

### One withdrawal, composed (`Journey/Withdraw.lean`)

- `Journey.withdraw_composed`: for one successful `withdraw nf tok amt rcpt root` from a reachable
  storage `σ` with the pinned verifier, given `WithdrawPost X`, `OwnerCallbackFree X`, the withdraw
  circuit rows (`WithdrawRows E C`: W3, W4, W5, W8, the W10 recipient), `PathFacts`,
  `Function.Injective E.cm`, A2 for this call (if the pinned verifier accepted the canonical
  public inputs, the extracted witness satisfies the withdraw relation), a model run `Run sup txs
  st` that `RepP` relates to `σ`, `PathTreeHyp` on the call's checked input and `CryptoHyp` on the
  extended run: the extracted witness (snapshot set to the current leaf count) is bound to the
  public words; the proof's root is the LeanIMT root of a prefix of the leaves that holds the
  note; the model's withdraw guard holds; the storage after the call represents the model
  post-state; the one token call is `transfer(token, recipient, amount)` of the witness; and the
  money theorems hold for the extended run.
- `Journey.withdraw_journey`: adds the client premise `hTransport` (the call's public-input vector
  equals `ClientInputs E n r nfw rootw`, the words of the intended note and recipient), and
  concludes that the token call carries the intended token, amount and recipient words.
- `Journey.withdraw_journey_of_history`: obtains the pre-state from an accepted history under the
  premises of `refinePL_run` for the extended history.
- `JourneyToy.journey_toy`: every premise instantiated on the toy pool, with the real LeanIMT
  fold on a depth-2 withdrawal path.

### Gas arithmetic (`Gas/Envelope.lean`)

In namespace `GasEnvelope`, with `cap = 2^24` and the memory cost `memoryCost a = 3a + a²/512`
(integer division):

- `memory_words_bound`: `memoryCost a ≤ cap → a ≤ 91,917` (with `boundary_costs`:
  `memoryCost 91,917 = 16,777,186` and `memoryCost 91,918 = 16,777,548`).
- `calldata_bytes_bound`: `21,000 + 10n ≤ cap → n ≤ 1,675,621`.
- `byte_envelope`: if `21,000 + 10n ≤ cap`, or `memoryCost a ≤ cap` and `n ≤ 32a` for some `a`,
  then `n ≤ 2,941,344` and `n < 2^30`.
- `aggregate_memory_bytes`, `frame_count`, `aggregate_inputs`, `aggregate_boundary_outputs`:
  bounds on totals over a transaction (32 × floor(2^24 / 3) bytes of memory; at most 167,772
  child frames at 100 gas each).

The written argument, not checked by Lean, connects this arithmetic to the EVM. Premises: the
transaction runs on a chain with the EIP-7825 cap (gas limit at most 2^24) and the EIP-7623
calldata floor (`21,000 + 10(z + 4u) ≤` gas limit for `z` zero and `u` nonzero bytes); each frame
starts with empty memory and pays the cumulative expansion cost `memoryCost a` at its largest
size `a` in words; forwarded gas is transferred, not duplicated; the decoded argument comes from a
canonical ABI encoding whose data region is backed. Steps: memory charges telescope within a
frame and the sum over frames is at most the cap, so each frame has `memoryCost a ≤ 2^24`; a
direct call's argument is inside the transaction data; a nested call's input and a `RETURN` or
`REVERT` output are regions of a frame's paid memory. So every canonical decoded `bytes`
argument of a gas-capped transaction has at most 2,941,344 bytes, inside the length domain
0..2^30 of the claim board's Kontrol rejection runs. This is the bound the board's `Proved*`
status (rows D1, D2 and the other guard rows) relies on. Not covered: non-canonical encodings,
forged length words, chains without the cap, gas starvation before a guard, raw precompile
output, and future changes to gas prices. No EVM execution is formalised.

## The premises

Each premise is a `Prop` the theorems take as a hypothesis; none is an axiom, and none is
discharged here for the deployment. The board rows are those of
`../evidence/2026-10-13-claim-board/CLAIM1-board.md`.

| Premise | Meaning | Board rows |
|---|---|---|
| `ConstructorPost X` | the constructor leaves every slot zero except the pinned verifier, the attestation registry and the owner | C1 |
| `Rollback X` | a reverted top-level call from a reachable state leaves storage unchanged | A11, X3 |
| `NoSetVerifier h` | no successful `setVerifier` call in the history; `Reach` restricts every contract premise to states reached this way | C1 |
| `OwnerCallbackFree X` | no successful owner-only call runs inside a token callback | A13 |
| `DepositPost H X` | on reachable states: token supported, amount nonzero, commitment new, verifier accepted the six canonical inputs, nested successes are owner calls, the only token call is `transferFrom(fund, pool, amt)`, and the storage after is one insert and one root record | D1, D2, D5, D6, S1, S2, X1, X2, T13 |
| `TransferPost H X` | distinct and unspent nullifiers, known root, two new distinct outputs, verifier accepted, no token call, storage after is two flags, two inserts, one root record | T1, T5, T6, T11, T12, T13, S1, S2, X1 |
| `WithdrawPost X` | amount nonzero, nullifier unspent, known root, verifier accepted, nested successes are owner calls, the only token call is `transfer(rcpt, amt)` on `tok`, storage after is one flag | W1, W6, W7, W10, S1, S2, X1 |
| `AdminStutter X` | each owner call writes only its own slot | G1 |
| `CircuitFacts E C Incl` | the circuit relations bind the public inputs: deposit amount below 2^128 and commitment, transfer owner key, membership, nullifiers, equal tokens, ranges, conservation, outputs; withdraw membership, owner, nullifier, public token and amount, recipient, range | the D, T and W circuit rows; discharged by citation of `circuits-lampe/` and `circuits-acir/`, not by import |
| `Function.Injective E.cm` | the commitment encoding into words is injective | none |
| `ExtractedWitnesses C ext h` | for every successful pool call of `h`, the extracted witness satisfies the circuit on the call's public inputs: an idealised, per-history form of knowledge soundness | A2 |
| `ValidRootsFresh X`, `TreeAppend H X` | in one successful call a `validRoots` flag turns true only for the new current root; a call appends its inserts to the tree slots in order. Both follow from the posts. | T1, W1 |
| `TreeLink H Incl Coll G W`, `TreeHyp Coll G W` | the global tree premises: a word the circuit relation takes to a prefix root is a leaf or a bad event `Coll` holds; the input words are nonzero and no bad event occurs | A9a, A9b, A12 |
| `RootsNonzero H h` | every root the history records is nonzero (`refine_run` only) | none |
| `PathFacts H E C ext pext` | the retained path of each checked input folds its commitment to the public root (the circuit's fold equation) | T3, W2 |
| `PathTreeHyp H G Q` | each checked input word is nonzero, and `LeanImt.Bad` does not occur on its retained path at any prefix of the history's leaves whose root the path reaches | A9b, A12 |
| `CryptoHyp P txs` | the gated model's hypothesis: no two distinct notes of the run share a commitment, no two distinct keys derive one public key | A1 |
| `TokenCallFacts X`, `PoolCallReadings X` | the token calls of each call kind; two source readings (the funder is not the pool; owner calls call no token) | D6, X2, W10, X1 |
| `Function.Injective E.tok` | the token encoding into words is injective | none |
| `NoOutsideDebit X K` | across a successful pool call the pool's balance changes at least by the stated credits minus debits, and outside transactions never decrease it | A10 |
| `TokenRollback X K` | a reverted pool call leaves the pool's balances unchanged | A10, A11 |
| `PoolStartsEmpty X K` | the pool holds no token at genesis | none |
| `NoOutsideCredit X K` | the converse bound: no positive rebase, no donation | A10 |
| `NoSelfWithdraw X h` | no withdrawal names the pool as recipient (the contract does not reject it) | W10 |
| `hTransport` (journey) | the call's public inputs are the client words of the intended note and recipient | client scope, outside claim 1 |

The hash `H` is free: no premise fixes its outputs. The tree premises (`TreeHyp`, `PathTreeHyp`)
and `CryptoHyp` are where hash properties enter; they are idealised per-history statements with no
proved reduction to a computational assumption about Poseidon.

## What the theorems say, and what they do not

- Conditional composition only. `X.Exec` and `X.Fail` are uninterpreted: no bytecode, Yul or EVM
  semantics is in this package, and no theorem says that the deployed contract satisfies a post.
  The posts summarise the contract's behaviour as read from the source; the claim board names the
  bounded Halmos and Kontrol runs that support parts of them.
- No production instantiation of any premise. The toy instances (`ToyRun.refine_run_toy`,
  `ProvToy.refineP_run_toy`, `PathToy.refinePL_run_toy`, `BalanceToyRun.refineB_run_toy`,
  `BalancePathToy.*`, `JourneyToy.journey_toy`) show that the premises can hold together, with a
  toy hash `a + b + 1`, verifiers that accept only fixed witnesses and identity encodings. They say
  nothing about the deployed pool, Poseidon or any real token.
- No token effects. Balances enter only through the named premises; no ERC-20 state is observed
  and no token is shown to satisfy A10. No recipient balance change is proved.
- No events, no gas (beyond the arithmetic above), no liveness, no reverts' reasons.
- The refinement holds up to snapshots: the model's root snapshot is erased and chosen again
  (`eraseSnap`). `refineP_run` concludes a `Step'` run (provenance root guard), not the model's
  window guard; `Run'.to_run` recovers a `Step` run with the same states. Exact retention of the
  last 100 roots (T13) is not proved; `repeated_root_evicts_early` shows a case where the contract's
  flags under-approximate its ring.
- The fold bridge is a statement about the circuits as Lampe reads them (see
  `../circuits-lampe/README.md`); the hash equality between Noir `hash_2` and Solidity
  `PoseidonT3` and the correspondence of the contract's root to the circuit's public root stay
  premises (A9b; `hash-agreement/` covers the field-level transcriptions separately).
- The faithfulness of `imtInsert` to `InternalLeanIMT._insert`, of the storage layout and of the
  posts to `ShieldedPool.sol` at ethsystems/pocs `a04b8b3` are human readings, supported by the
  mutant checks above, not by a machine link to the Solidity source.

## Controls

[controls/](controls/) holds the hand-written controls and `controls/gen/` the generated ones;
[fold-bridge/controls/gen/](fold-bridge/controls/gen/) those of the fold bridge. Each `fail_*`
control must fail to compile with the first error recorded in the `EXPECTED.tsv` beside it; each
`pass_*` control must compile with the standard axioms. A failing control shows that the original
proof does not prove the changed statement; it does not show that the changed statement is false.
Where falsity matters, a theorem in the modules proves it (`Toy.repCore_no_window_inclusion`,
`Toy.treeLink_needs_nonzero`, `ProvToy.bad_breaks_prov`, `BalanceToy.eq_needs_rollback`,
`BalanceToy.eq_needs_noOutsideDebit`, `BalanceToy.self_withdraw_breaks_eq`,
`PathToy.control_planted_bad`, `PathToy.old_premise_false_on_toy`,
`FoldBridge.Checks.control_flip_false`, `FoldBridge.Checks.control_depth_false`). Three controls
fail by a missing name by design, because the name is what the change removes:
`fail_rep_without_valid_roots` (the field `valid`), `fail_treelink_without_nonzero` (the
hypothesis `hne`) and `fail_bridge_bad_field_no_range` (the range hypothesis `hL`).

| Control | Change |
|---|---|
| `fail_rep_without_valid_roots` | the window-inclusion proof on `Rep` without its valid-roots field |
| `fail_treelink_without_nonzero` | the depth-0 tree link without the nonzero-leaf restriction |
| `fail_prefixroot_drop_leaf` | provenance moved to a shorter leaf list |
| `fail_prov_step_without_fresh` | the provenance step with a freshness premise a root record does not meet |
| `fail_balance_without_rollback` | `bal_eq_ledger` without `TokenRollback` |
| `fail_journey_without_path_tree` | `withdraw_composed` without `PathTreeHyp` |
| `fail_journey_swapped_words` | the journey's token call with amount and recipient swapped |
| `pass_input0_ballast_refuted` | an earlier transfer guard (input 0 may be ballast) accepts a transfer the model's guard rejects |
| `fail_imt_fold_direction_flipped`, `fail_imt_no_carry`, `fail_imt_proof_left_bit_true` | copies of `Tree/LeanImt.lean` with the fold direction, the carry rule or a proof bit changed |
| `pass_imt_unchanged` | the unchanged copy |
| `fail_bridge_direction_flipped`, `fail_bridge_depth_plus_one`, `fail_bridge_bad_field_no_range` | copies of `FoldBridge/Bridge.lean` with `merkleRoot_val` or `bad_field` changed |
| `pass_bridge_unchanged` | the unchanged copy |

## Trust base

- The Lean kernel and the three standard axioms; Mathlib at `0df444a` (tag `v4.33.1`), the
  parent's pin.
- The gated model files the package imports (pinned in `PINS.sha256`); whether they say what
  spec 2 says is the parent's human reading (`../REVIEW.md`).
- For the fold bridge only: the trust base of `../circuits-lampe/` (the Lampe fork at its pinned
  commit, its stdlib, the extractor that produced the committed Lean sources).
- Not trusted: the proof modules, the census, the scans and the controls. They are checks
  against mistakes, not against a hostile package: code that runs during elaboration could change
  what the census prints.

## Pins

[PINS.sha256](PINS.sha256) holds the sha256 of every file outside the package that the results
rest on: the 13 model modules the package imports (directly or through each other), the parent's
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, this package's toolchain and manifest,
and for the fold bridge the four `circuits-lampe` modules it imports with that package's
`lakefile.toml` and `PINS.sha256` (which pin Lampe and the extracted circuits).
`scripts/pins.py` checks them and that the pinned model modules are exactly the import closure.
`lakefile.toml` shares the parent's dependency checkouts (`packagesDir = "../.lake/packages"`).

## Re-check

Install git, bash, python3 (3.10 or later), sha256sum and elan. The first run downloads
Mathlib's checkout and prebuilt oleans into `../.lake/packages` (about 7.5 GB, shared with the
parent package); the fold-bridge stage also downloads the Lampe fork and builds part of
`../circuits-lampe` (see its README).

```
cd refinement
scripts/check.sh      # expect the last line: CHECK PASS: ...
```

`FOLD_BRIDGE=0 scripts/check.sh` skips the fold-bridge stages (a few minutes instead of about
an hour from a fresh copy). `JOBS` sets how many controls and circuit modules compile at once.

`scripts/check.sh` runs, in order:

1. the tools: Lean 4.33.1 through lake, python3;
2. the pins (`scripts/pins.py`);
3. a source scan (`scripts/scan.py`) of every Lean file of the package for `sorry`, `admit`,
   `native_decide`, `axiom`, `opaque`, `extern`, `implemented_by`, `unsafe` and `skipKernelTC`, of
   the pinned model files' code for the same, and of the lakefiles for kernel options;
4. the rename check (`scripts/check-rename.py`, below);
5. regeneration: the generated controls must equal the output of `scripts/gen-controls.py`;
6. the build: `lake build` of the five libraries `Refinement`, `Tree`, `Balance`, `Journey`
   and `Gas` (and of the parent modules they import);
7. the census (`Census.lean`, `scripts/census.py`): every theorem of every package module,
   auxiliary ones included, depends on a subset of the three axioms; no package module declares
   an axiom or an opaque constant; the census imports every module; and the theorems, their
   printed statements and the SHA-256 of their raw types equal `statements/INVENTORY.md` and
   `statements/RAW.sha256`;
8. the controls (`scripts/controls.py`) against `controls/EXPECTED.tsv`;
9. the fold bridge: `scripts/build-fold-bridge.py` (the circuits-lampe build steps, then the
   bridge with the model and tree modules it imports, compiled from source into
   `build/fold-bridge/lib`), its census (`fold-bridge/Census.lean`, `statements/FOLD-BRIDGE.md`,
   `statements/FOLD-BRIDGE.sha256`) and its controls (`fold-bridge/controls/EXPECTED.tsv`).

[RESULT.md](RESULT.md) records a run: counts, times and peak memory.

## Layout

- `Refinement/`: `Storage` (the storage model, calls, `Contract`, `Accepted`), `Rep` (the
  representation relation), `Post` (the premise structures), `Compose` and `Cases` (the
  induction and `refine_run`), `NonVacuity` (the toy pool), `Provenance`, `ProvenanceModel`,
  `ProvenanceRefine` and `ProvenanceNonVacuity` (root provenance, `Step'`, `refineP_run`),
  `PathLocal` and `PathLocalNonVacuity` (`refinePL_run`).
- `Tree/`: `LeanImt` (the LeanIMT tree against the circuit fold), `Checks`.
- `Balance/`: `Basic` (the chain, the stated deltas, `refineB_w9`, `refineB_run`), `NonVacuity`,
  `ToyRun`, `PathLocal`, `PathLocalNonVacuity`.
- `Journey/Withdraw.lean`: the composed withdrawal and its toy instance.
- `Gas/Envelope.lean`: the gas arithmetic.
- `fold-bridge/`: `FoldBridge/Bridge.lean`, `Compose.lean`, `Checks.lean`, `Census.lean`,
  `controls/`.
- `Census.lean`; `statements/`: the inventories and raw-type hashes.
- `controls/`: the hand-written controls, `controls/gen/`, `controls/EXPECTED.tsv`.
- `scripts/`: `check.sh`, `pins.py`, `scan.py`, `census.py`, `controls.py`, `gen-controls.py`,
  `build-fold-bridge.py`, `targets.py`, `rename.py`, `check-rename.py`, `rename-map.txt`,
  `rename-origins.txt`.
- `PINS.sha256`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `RESULT.md`.

## Claim board rows

The rows of `../evidence/2026-10-13-claim-board/CLAIM1-board.md` whose Lean evidence this package
holds:

- T1, W1: root provenance (`accepted_root_provenance`, `transfer_root_provenance`,
  `withdraw_root_provenance`), under the provenance premises.
- X3: the conditional composition (`refineP_run`, `refinePL_run`, `refine_run`) and the composed
  withdrawal (`Journey.withdraw_journey_of_history`, `JourneyToy.journey_toy`).
- T3, W2: the membership composition on the circuit side (`FoldBridge.withdraw_member_or_bad`,
  `FoldBridge.transfer_member_or_bad`) and the path premise of the refinement (`PathFacts`).
- A9a: the LeanIMT tree and fold correspondence (`LeanImt.*`) and the fold bridge
  (`FoldBridge.*`).
- A9b, A12, A13: the premises `PathTreeHyp`, `TreeHyp` and `OwnerCallbackFree`, named and used;
  nothing proves them.
- W9: the balance bound (`refineB_w9`, `refineBPL_w9`); W10: the stated withdrawal deltas
  (`withdraw_debits_pool`, `withdraw_credits_recipient`) and the composed token call.
- D1, D2 and the other `Proved*` rows: the arithmetic of the gas argument (`GasEnvelope.*`); the
  Kontrol runs those rows also rest on are not in this package.

## Earlier names

The modules were first written with working names. `scripts/rename-map.txt` maps each earlier
module, namespace and control name to its name here, and the labels that the claim board and the
earlier reports use to the results here. Declaration names did not change.
`scripts/check-rename.py` applies the map backwards to every module (for the fold bridge also the
map of `../circuits-lampe/scripts/rename-map.txt`), removes the comments, and compares the SHA-256
of the result with the original's in `scripts/rename-origins.txt`: the modules differ from their
first form only in names and comments.
