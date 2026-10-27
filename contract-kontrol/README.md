# contract-kontrol: Kontrol proofs about the pool contract at `a04b8b3`

This package holds the symbolic proofs about `ShieldedPool.sol` of ethsystems/pocs (public) at
`a04b8b3`, and about its libraries, that the claim board ([../BOARD.md](../BOARD.md))
cites under its contract rows: the rejection guards of deposit, transfer and withdraw, the withdraw
success path (marking before payout, the payout call, the verifier inputs), canonical public inputs
and their order, local checks of the tree insertion loop, and the frame of the PoseidonT3 library.
Each Kontrol proof runs in Kontrol 1.0.255 (KEVM, the K framework) in a Docker image pinned by
digest, against the pool source exported from the git submodule `pocs/`.
Each Kontrol harness proof (each `prove` run of `harness/<suite>/runs.tsv`) has must-fail siblings
(mutants): the same proof against a pool or library with one change, which must fail at a stated
output. Two parts are checked another way. The archived K claims of the insertion loop
(`harness/insert-loop/k/`) have no must-fail proofs: the mutant verdicts of their earlier run were
withdrawn, and concrete controls (`insert-loop` run `controls`) replace them. The PoseidonT3 frame
suite (`poseidon-frame`) is a set of Halmos checks; its mutant is a witness that must fail an
assertion, not a Kontrol output. `check.sh` runs the selected runs and compares every exit status
and every verdict with `EXPECTED.tsv`; [RESULT.md](RESULT.md) records the runs on this machine.

The parts are about different builds. The Kontrol harness proofs are statements about the EVM
bytecode that solc 0.8.37 builds from the pinned source for the Prague EVM. The archived K claims
are statements about the LeanIMT library runtime of an earlier build by solc 0.8.33 (the compiler
metadata inside the claims says so), under KEVM's Cancun schedule (`<schedule> CANCUN`). Their
controls run that archived runtime, and copies of the library source that solc 0.8.37 compiles for
Cancun. The `poseidon-frame` checks are about the PoseidonT3 runtime that solc 0.8.37 builds for
Osaka. Each holds only under KEVM's or Halmos's semantics and the trust base below, inside its own
scope. None is a proof of the contract, of any deployment, or of claim 1. The model gate
(`scripts/gate.sh`) never runs them and nothing here changes the claim in the parent README.

Which numbers this machine reproduced: [RESULT.md](RESULT.md) has one table per suite. No single
`check.sh` invocation of 2026-10-24 ran every suite and ended `CHECK PASS`. The suite comparisons
that matched come from separate invocations: `guards-patched` (run 3, compared afterwards on its
work directory); `withdraw-success`, `guards-stock`, `insert-loop` and `poseidon-frame` (run 5,
whose last line was `CHECK FAIL` because the `public-inputs` build was stopped); the `public-inputs`
build and replays only (run 6); `insert-loop` again (run 7); and every run of `public-inputs`
(run 8). So every run of every suite has matched, but no single invocation covered them all. The
`check.sh` and `compare.py` of those runs predate the stricter checks that RESULT.md lists.
**Packaged, not run:** the archived K claims in `insert-loop/k/`, about the 0.8.33 build;
`check.sh` does not run them.

## Suites

| Suite | Runs | Board rows |
|---|---|---|
| `guards-stock` | `withdraw`, `deposit`, `transfer` | D1, D2, D3, D6, T1, T5, T6, W1, W6 (rejection), W7, W8 |
| `guards-patched` | `withdraw` | W1, W6 (rejection), W7, W8, below 2^64 |
| `withdraw-success` | `token-above-0x11`, `two-tokens`, `replay` | W6, W10, X2 (withdraw half), S2 (withdraw) |
| `public-inputs` | `canonical`, `order`, `fixed-token`, `replay` | S1, S2, W6, W10 |
| `insert-loop` | `rejections`, `controls` (and the K claims in `k/`) | the duplicate-leaf, fresh-output, marking and ordering rows (scoped components) |
| `poseidon-frame` | `frame` | A5 (the real PoseidonT3 is a pure function) |

[scripts/rename-map.txt](scripts/rename-map.txt) maps each earlier run label to the suite and run
here, and every earlier file, contract, test, mutant and module name to its name here.

Common to every Kontrol suite unless its section says otherwise ("the common scope"):

- Canonical ABI calls, made by the test contract with Solidity's own encoder, zero value. Other
  calldata layouts (non-canonical offsets, trailing bytes) are not covered.
- Pool storage symbolic (`kevm.symbolicStorage`) except three pins: slot 108 holds the mock
  verifier, slot 109 the registry, and the reentrancy slot `0x9b77...5f00` holds 1 (not entered).
  Registry storage symbolic.
- Fixed code: the pool (or one mutant), the real LeanIMT library code at its linked address
  `0xA1001`, and the mocks of the suite. No PoseidonT3 runs on any path checked here (every path
  stops at or before the verifier, or is a withdraw, which does not hash).
- Code compiled by solc 0.8.37 for the Prague EVM (forge 1.5.1's default), optimizer 100 runs. (The
  archived K claims of `insert-loop/k/` are the exception: 0.8.33, Cancun; see `insert-loop`.)
- Mocks that record and move no balances: verifiers that compare or trip, a registry with a
  symbolic root, recording tokens. Token movement (A10) stays an assumption.
- Gas not modelled (Kontrol's default, no `--use-gas`). A call that runs out of gas is not covered.
- KEVM and Kontrol's keccak lemmas in force (injectivity; a keccak of a symbolic argument is never a
  concrete value), so mapping keys stay apart from the pinned slots.
- Kontrol's environment ranges: block number in (2^24, 2^32), timestamp in (2^30, 2^35).
- `bytes` lengths: one symbolic length per `bytes` argument, content symbolic. The stock KEVM bounds
  each length at 2^30 bytes (`abi.md` line 456, an `ensures` on the `#bytes` encoding rule) and
  Kontrol at below 2^64. The patched KEVM (`kevm-patch/`) deletes the 2^30 `ensures`, so a length
  is any value below 2^64. Each suite names which KEVM it uses.

A FAILED mutant is checked here at the level of Kontrol's verdict and the exact output bytes of its
failing node (the revert data, read from the saved proof graph). The earlier runs also checked that
each failing node is feasible: every path constraint true at one concrete point, and a forge replay
at that point reaching the same error. This package carries the replays (`*Replay.t.sol`, run by
`check.sh` on the host); it does not carry the per-node constraint evaluation.

### guards-stock: rejection guards, lengths 0 to 2^30

Harness `harness/guards-stock/RejectGuards.t.sol`, stock KEVM. For each of the 13 guards before the
verifier (deposit `:145-149`, transfer `:195-204`, withdraw `:255-263`): with every earlier guard of
the same function passing and this guard's condition failing, the call from a symbolic caller
(`vm.prank`) reverts, and its revert selector is this guard's error. The verifier mock reverts with
its own marker on every call, so an equal selector also shows the verifier was not reached. No
storage check after the call: unchanged storage follows from the revert under KEVM's call
semantics.

Scope line (exact): canonical ABI calls, zero value, symbolic caller, symbolic pool storage with
slots 108, 109 and the reentrancy slot pinned, registry storage symbolic; proof and payload of
symbolic length 0..2^30 and symbolic content (stock KEVM); fixed code; trip verifier; gas off; KEVM
keccak lemmas.

Mutants (`mutants/guards-stock/`): 13, one per guard, each replacing that guard line by a comment.
Each must fail; its failing node is the test's `assert` (Panic 0x01), because a later guard fires
with its own selector. A mutant failure shows that the selector assertion catches the removed
guard. It does not show that the verifier becomes reachable.

Not shown: rejection at lengths above 2^30 (see `guards-patched` for withdraw; the board's
GAS-LEMMA argues that no transaction under the EIP-7825 gas cap carries one), non-canonical
calldata, out-of-gas behaviour, anything after the verifier, the canonical-input check (`:163`,
`:218`, `:275`; the earlier file also held those checks, they did not close, and this
package leaves them out; see `public-inputs`).

### guards-patched: withdraw guards, proof lengths below 2^64

Harness `harness/guards-patched/LongProofWithdrawGuards.t.sol`, patched KEVM. The four withdraw
guards (W7 `:255` zero amount, W8 `:256` amount at least 2^128, W6 `:260` nullifier spent, W1
`:263` unknown root), with the same property as above, for every proof length below 2^64. Two
harness changes, forced by Solidity: the scalars travel in a memory struct, and the pool is called
with a high-level try/catch, which encodes the arguments without allocating them (an allocation
near 2^64 bytes panics).

Scope line (exact): as `guards-stock`, except that the proof has a symbolic length below 2^64 (the
patched `abi.md`), and withdraw has no payload.

Mutants (`mutants/guards-patched/`): the four withdraw guard removals. The earlier run read the
failing node of the zero-amount mutant from its saved graph (no verdict line); the other three are
added in this package and have no earlier verdict (`EXPECTED.tsv` marks them "new").

Not shown: the deposit and transfer guards below 2^64. Two attempts did not close (the test's own
decoder rejected a second `bytes` argument near 2^64; a one-`blob` split ran 22 minutes without
closing). They stay at 0..2^30 (`guards-stock`). The test contract also holds three
canonical-input checks for withdraw (`prove_noncanonical_*`); they did not close in the earlier run
and no run here selects them.

### withdraw-success: the success path with the token argument above 0x11

Harness `harness/withdraw-success/WithdrawSuccess.t.sol`, patched KEVM, with the bytes-prefix lemma
(`lemmas/bytes-prefix.k`). One body checks every path of `withdraw(proof, n, token, a, rcp, r)`:
the verifier mock compares its inputs with `[n, token, a, rcp, r]` (length 5, full 256-bit words)
and answers with a symbolic `accept` flag; a revert with its `Diverged` marker fails the proof
(`W10Inputs`). On success: the verifier said yes (`W10VerifierBypassed`), exactly one retained
recorded call reached the two recording tokens and it went to `token` (`W10Calls`,
`W10WrongToken`), that token saw `nullifiers[n] == true` at its call (`W6NotMarkedAtPayout`) and
the flag is set after (`W6NotMarkedAfter`), neither token saw any other call (`W10Calls`), and the
call was `transfer(rcp, a)` from the pool (`W10Args`).

Run `token-above-0x11` (`prove_success_token_above_0x11`), scope line (exact): withdraw success
path. Token argument: any address t with t > 0x11 and t != the cheatcode account, within a
fixed-code environment: two armed recording tokens, seven other deployed contracts, no code
elsewhere. Successful withdrawals exist only on the two recording mocks. Fixed caller (the test
contract). Symbolic n, a, rcp, r, acc at full width. Symbolic pool storage except slot 108, slot
109 and the reentrancy slot. Proof length < 2^64, content symbolic. Comparison verifier mock; the
inputs are compared in its decoded body, so a path supplies a comparison only when the verifier
call reaches that body, which needs `ceil32(proof.length) <= 2^64 - 97` (the bound that BOARD.md
row S2 states for the same withdraw call). Recording token mocks that move no balances. Kontrol 1.0.255, the patched `abi.md`, the
bytes-prefix rule, gas off, KEVM keccak lemmas.

Run `two-tokens` (`prove_success_two_tokens`), scope line (exact): the same body, with the token
argument symbolic and assumed equal to one of the two recording tokens (`0xf000...000b` or
`other` at `0xc7183455...0bb1`; both have bit 159 set); otherwise as above. The earlier run of this
proof did not load the bytes-prefix rule; here the suite builds once with it, so this run has it
too. The rule only removes paths whose constraints are false (below), so it cannot turn a failing
proof into a passing one by itself; it can make a proof close that would otherwise explore an
impossible branch.

Why above 0x11: KEVM's `isPrecompiledAccount` is `0 < t <= #precompiledAccountsUB(SCHED)`, at most
17 (`0x11`) over all schedules. Without the bound, the branch of a token with no account stalled on
`#precompiled(token)`. Addresses `0x00` to `0x11` are not covered.

Mutants (`mutants/withdraw-success/`), with the output each must fail at:

| Mutant | Change | Output of the failing node |
|---|---|---|
| `FIXED_TOKEN` | pays one fixed token (`0xF000...000B`), not the named one (`:286`) | `0x7fa6412e` `W10WrongToken()` |
| `LATE_MARK` | marks the nullifier after the payout (`:283`, `:286`) | `0xe3e0fc25` `W6NotMarkedAtPayout()` |
| `SWAP_INPUTS` | nullifier and root swapped in the verifier inputs (`:267`, `:271`) | `0x1987cd34` `W10Inputs()` |
| `DROP_BIT253` | bit 253 of the nullifier input cleared (`:267`) | `0x1987cd34` `W10Inputs()` |
| `PAY_CALLER` | pays `msg.sender`, not the recipient (`:286`) | `0x0bc6283d` `W10Args()` |
| `SKIP_VERIFIER` | the verifier is not called (`:278`) | `0x5b1cfd09` `W10VerifierBypassed()` |

In the earlier `token-above-0x11` run, the `FIXED_TOKEN` failure was at a token with no code
(`0x1234567` in its replay), a path a two-token scope cannot reach. `LATE_MARK` is the control of
W6; the other five are controls of W10.

Not shown: arbitrary token code or behaviour; token movement (A10); proof binding (A2); token
addresses `0x00` to `0x11`; a symbolic caller. The symbolic-caller form of the same body
(`prove_caller_two_tokens`, `vm.prank` with a symbolic caller) does not close in Kontrol 1.0.255:
the prank splits once per existing account and its unconstrained default branch splits again in the
same way. No run here selects it. That `withdraw` never reads `msg.sender` is a source reading (the
pool reads it only in `onlyOwner`, the constructor and `deposit`), not a result of this package.
A Halmos run of the same body with a symbolic caller is the `caller` suite of
[../contract-halmos/](../contract-halmos/README.md).

The bytes-prefix rule (`lemmas/bytes-prefix.k`, module `BYTES-PREFIX-LEMMAS`, four
`[simplification]` rules, one fact in four orientations): when `B1` and `B2` are concrete,
`lengthBytes(B2) <= lengthBytes(B1)` and `substrBytes(B1, 0, lengthBytes(B2)) =/= B2`, then
`B1 == B2 +Bytes X` is false (as `==K` both ways and as `#Equals` both ways, to `#Bottom`).
Soundness: if `B1 == B2 +Bytes X`, then `B2` is a prefix of `B1`, so `substrBytes(B1, 0,
lengthBytes(B2)) == B2`; each rule is the contrapositive. Why it is needed: after a token call that
returned no data, OpenZeppelin's `SafeERC20._safeTransfer` compares `mload(0x00)` with 1, while
memory still holds the selector `0xa9059cbb` and `to`. Kontrol 1.0.255 leaves
`b"\x00..\x01" == b"\xa9\x05\x9c\xbb" +Bytes #range(#buf(32, rcp), 0, 28)` undecided, although it
is false for every `rcp` (the first byte differs), and without the rule the stock proof fails at a
node that no real execution reaches. The rule is trusted: K checks no proof of it. The board records
a Lean proof of the rule's content (2026-10-11); that Lean file is not in this repository, and its
integration into Kontrol stays trusted either way.

### public-inputs: canonical inputs, input order, and the fixed-token withdraw

Harnesses `harness/public-inputs/PublicInputs.t.sol` and `CanonicalInputs.t.sol`, patched KEVM, one
build.

Run `canonical` (rule S1). A verifier mock checks every input word in its decoded body: a word
`>= P` (the BN254 scalar field modulus) reverts `NonCanonical()`, any other input reverts
`Reached()`; the pool catches neither, and each entry point makes one verifier call. Property: on
every path of `deposit`, `transfer` and `withdraw` that reaches the decoded verifier body, every
public input is `< P`. A call that the mock's ABI decoder rejects, or that reverts before the body
runs, supplies no input comparison. Scope line (exact): canonical ABI calls, zero value, caller the
test contract (deposit's funding address is the test contract), symbolic pool storage with slots
108, 109 and the reentrancy slot pinned, registry storage symbolic, token a symbolic address;
withdraw proof of symbolic length < 2^64 and content, where only paths with
`ceil32(proof.length) <= 2^64 - 97` reach the decoded body (the bound that BOARD.md row S2 states
for the same withdraw call); deposit and transfer with an empty proof and a payload of symbolic
length < 2^64 and content; inputs observed in the decoded mock body only; fixed code; gas off; KEVM
keccak lemmas. Mutants: `DEPOSIT_CANONICAL`, `TRANSFER_CANONICAL`, `WITHDRAW_CANONICAL` (one canonicality call removed, `:163`, `:218`, `:275`),
each failing at `0xb9e93ed0` `S1NonCanonical()`; three witnesses (`prove_witness_*_canonical_mustfail`)
must fail with Panic 0x01, showing the verifier is reachable with canonical inputs. The boundary
mutant `BOUND_GT` (`>=` to `>` at `:361`) has no Kontrol verdict; its forge replay fails as
required.

Run `order` (rule S2). The comparison verifier must receive exactly
`[c, t, a, funder, registry.root(), keccak(payload) mod P]` (deposit) or
`[n0, n1, c0, c1, r, keccak(payload) mod P]` (transfer), the circuits' order. Scope line (exact):
as `canonical`, deposit and transfer only, empty proof; the order is observed in the decoded body
of the comparison mock. Mutants `DEPOSIT_SWAP_45` and `TRANSFER_SWAP_45` (inputs 4 and 5 swapped) fail at `0x794445cf` `S2Inputs()`; two witnesses must
fail with Panic 0x01.

Run `fixed-token` (rules W6, W10 with one token). The withdraw body of `withdraw-success` in its
first form: the token is fixed (`0xf000...000b`), a second recording token must get no call
(`W10OtherToken`), no bytes-prefix rule. Scope line (exact): as `withdraw-success`, with the token
fixed; the inputs are compared in the decoded body of the comparison mock, which only paths with
`ceil32(proof.length) <= 2^64 - 97` reach (BOARD.md row S2). Mutants `LATE_MARK`, `SWAP_INPUTS`,
`DROP_BIT253`, `PAY_CALLER`, `SKIP_VERIFIER` with the outputs of the table above; a witness must fail with Panic 0x01. The `token-above-0x11` run covers
this token as one case, with a stronger body.

Rerun here on the 0.8.37 build (run 8 of RESULT.md): the build, `canonical` (9 of 9), `order` (6
of 6), `fixed-token` (7 of 7) and the 36 replays gave the verdicts and failing outputs of
`EXPECTED.tsv`, which first came from the 2026-10-01 run on the 0.8.33 build.

Not shown: deposit and transfer with a nonempty symbolic proof and a symbolic payload together (the
`*_split` bodies, one `bytes` split at a symbolic index, did not finish in the earlier run and no
run here selects them); a caller other than the test contract; the verifier's own soundness; a
verifier swapped by `setVerifier`; tree insertion.

### insert-loop: the tree insertion loop

Run `rejections` (Kontrol, stock KEVM; `TreeRejections.t.sol`, `TreeHarness.sol`). A minimal
harness owns one `LeanIMTData` at slot 0, as the pool's tree, and calls the real LeanIMT library
code at its linked address. From fully symbolic tree storage (any size, any depth, any `sideNodes`
and `leaves`), `insert(leaf)` reverts with `LeafGreaterThanSnarkScalarField` for `leaf >= P`, with
`LeafCannotBeZero` for 0, and with `LeafAlreadyExists` when `leaves[leaf] != 0` and `0 < leaf < P`.
Mutants (`mutants/insert-loop/`): each removes one of the three checks from a copy of
`InternalLeanIMT.sol` (and points a renamed copy of `LeanIMT.sol` at it; the copy imports
`Constants.sol` by its package path); each must fail with Panic 0x01. As with the pool guards, a
mutant fails because a later check fires (for the zero and field checks, `LeafAlreadyExists` when
`leaves[leaf] != 0`; for the duplicate check, an arithmetic panic at size `2^256 - 1`). Scope line
(exact): one call of the harness's `insert` with zero value, symbolic tree storage, PoseidonT3
replaced by a keccak stub at `0xA1002` (no rejection path hashes), gas off, KEVM keccak lemmas.

Run `controls` (a Foundry project, `harness/insert-loop/controls/`, run on the host, no Kontrol).
Concrete controls for the K claims about the zk-kit LeanIMT `_insert` loop (below): six witnesses,
two depths for each of three one-byte mutants of the library runtime (`M1`: pc 2158 KECCAK256 to
MUL, the zero-bit branch writes slot 0; `M2`: pc 2149 PUSH1 2 to 3, the zero-bit branch writes
`leaves[level]`; `M3`: pc 2209 PUSH1 3 to 2, the final leaf write goes to `sideNodes[leaf]`). Each
witness runs twice: on copied Solidity regions of the library (`vendor/`, checked equal to zk-kit at
the pinned rev) and on the runtime bytes of the K claims (`runtime/`, with entry and exit adapters,
`runtime/instrumentation.json` lists every changed offset). The stock code passes all 21 tests;
each of the 20 mutant controls fails at its named postcondition; the stub comparison passes in both
runs. `tools/check_witnesses.py` recomputes all 40 observations independently (`cast keccak`) and
checks the source copies, the source diffs, the extracted regions and the one-byte runtime changes.
Scope: local segment entries with the data preconditions of the K claims; no whole-call
reachability, PoseidonT3 replaced by a keccak stub (A5).

The K claims (`harness/insert-loop/k/`): `loop1-spec.k` (loop-frame: from the loop head, pc 1964,
the loop reaches its exit with level = depth and slots 0 and 1 unchanged, for every depth 0..256),
`loop3-spec.k` (loop-frame2: also preserves one mapping key `keccak(K ++ M)` with `M != 2` or `K`
outside the visited levels), `loop2-spec.k` (loop-exact: storage and node after the loop are
`#lstore`, `#lnode` of `loop-funcs.k`), `loop5e-spec.k` (post-loop-exact: from the exit to the
return, `S[0 <- INDEX+1][sideNodes[DEPTH] <- NODE][leaves[LEAF] <- INDEX+1]`), and the mutant
claims `loop1m`, `loop3m2`, `loop5em3`. They are about the library runtime of the earlier solc
0.8.33 build (its metadata is in the claims) under KEVM's Cancun schedule, not about the 0.8.37
Prague build of the Kontrol suites. The earlier run (by 2026-10-01) proved the four claims (`kevm
prove` on a definition built with `loop-funcs.k`, each final cover re-decided by the Kore
implication check after the faster booster check had found it); the must-fail verdicts of that run
were withdrawn because their failing nodes were not feasible, and the controls above replace them.
**Not rerun here, and `check.sh` does not run the K claims.** They are archived specifications
without a reproduced proof procedure. Each claim requires `foundry.k`, the K definition that
`kontrol build` generated for the earlier project; this package neither carries nor regenerates
it. The earlier proof also needed manual graph steps (removing covers, pruning a graph, resuming
with another implication check) that no script here records. Two corrections to the earlier
description of these claims: the post-loop claim writes `INDEX + 1` to slot 0 and `leaves[LEAF]`
(count growth needs an extra entry relation), and `loop-frame2` preserves one mapping key, not
every unvisited entry.

Not shown: entry relations, the depth update, whole-call composition, the real PoseidonT3 in the
loop, a general caller frame.

### poseidon-frame: the PoseidonT3 library is a pure function

This suite is a Halmos 0.3.3 check, not a Kontrol proof; it is here because the board lists it with
the Kontrol rows. `harness/poseidon-frame/` is a small Foundry project run on the host.
`scripts/rebuild.py` compiles `PoseidonT3.sol` of the pinned poseidon-solidity 0.0.5 package with
solc 0.8.37 and the settings of the pool build (`inputs/solc-settings.json`: optimizer 100 runs,
Osaka, the library links and remappings, which enter the metadata) and requires that the runtime,
with the library address `0xA1002` in its call-protection slot, equals the bytes the tests etch,
byte for byte (16,466 bytes), and that the creation code equals the one of `test/Deployment.t.sol`.
`scripts/scan.py` decodes the executable instructions (up to the compiler's INVALID fence; no valid
jump destination after it) and requires none of SSTORE, SLOAD, TSTORE, TLOAD, any call, create or
self-destruct, any LOG, and none of the caller, origin, balance, block or gas reads; one ADDRESS (the
library's call-protection check).

Halmos, on the real bytecode with generic symbolic storage of the caller and the library, all
inputs `x`, `y` over every uint256:

| Check | Expected | Says |
|---|---|---|
| `check_frame_equal_inputs` | PASS, 1 path | two delegatecalls succeed, return 32 bytes each, agree; an arbitrary slot and the whole modelled state are unchanged |
| `check_call_context_same_result` | PASS, 1 path | a direct call and a delegatecall return the same word and change no state |
| `check_wrong_selector` | PASS, 2 paths | every other selector reverts with empty data, at calldata length 68 |
| `check_short_calldata` | PASS, 132 paths | symbolic calldata of every length 0 to 67 reverts with empty data |
| `check_mutant_witness` (mutant) | FAIL, 1 valid model | a copy that adds `sstore(0, not(sload(0)))` fails the frame assertion at `x = y = slot = 0` |

Forge replays: the real runtime keeps slot 0 at a concrete call, the mutant changes it to all ones
(`MutantReplay` must fail); `DeploymentTest` deploys the creation code and checks the runtime.

Scope line (exact): calls `0x561558fe || uint256(x) || uint256(y)`, zero value, enough gas and call
depth, normal fresh memory; the pinned runtime at `0xA1002`. Not shown: Poseidon's arithmetic or
any hash property (Halmos abstracts some multiplications and remainders by deterministic
functions); gas exhaustion; calldata longer than 68 bytes; the use of this rule inside the
insertion-loop claims, which still run with a keccak stub (A5). The earlier fully symbolic mutant
runs hit memory limits and are not results; the mutant control is the fixed-point witness above.
Trust: Halmos 0.3.3 and its solvers (yices 2.6.4, z3 4.12.6, installed from
`requirements-halmos.txt`, every package pinned by sha256; `check.sh` checks the installed Python
3.12 environment against the RECORD pins of `PINS.txt` and runs Halmos as `python -I -m halmos`),
forge and solc.

## Trust base

- KEVM and Kontrol semantics as built into the image: Kontrol 1.0.255, image
  `runtimeverificationinc/kontrol@sha256:858f004144d61b005997f56bb8b7cd15673850286c96e0e5ec0502d9c9a9e204`
  (tag `ubuntu-jammy-1.0.255`), with its K backends (booster and Kore), z3, and the KEVM and Kontrol
  keccak lemmas. A wrong rule there can make a wrong proof pass.
- The patched `abi.md` (`kevm-patch/abi.md`, sha256 `e249e9e2...7a88`) for `guards-patched`,
  `withdraw-success` and `public-inputs`: the image's own file (sha256 `878f7732...f95e`) with one
  deletion at line 456, the `ensures lengthBytes(BS) <=Int 1073741824` of
  `rule #enc(#bytes(BS)) => #encBytes(lengthBytes(BS), BS)` (`kevm-patch/abi.md.diff`). K adds an
  `ensures` to the path condition, so the deletion removes an assumption and adds none; the
  remaining bound below 2^64 comes from Kontrol's argument ranges. The change is a commit of a
  fork of KEVM: `https://github.com/oskarth/evm-semantics`, branch `shielded-pool-model`, commit
  `6795265`, one commit on top of upstream tag `v1.0.921` (`d4bf484`), the kevm-pyk version inside
  the image. The fork is not built into an image: the proofs run the pinned upstream image with the
  fork's `abi.md` mounted over the image's own. `check.sh` reads the image's file and requires that
  it plus the diff gives the pinned file, and, when a selected run mounts the patched file (unless
  `KEVM_FETCH=0`), fetches the fork commit and
  requires that its parent is the `v1.0.921` commit, that its `abi.md` is `kevm-patch/abi.md`, and
  that the parent's `abi.md` is the image's.
- The bytes-prefix rule (`lemmas/bytes-prefix.k`) for `withdraw-success` (all its runs), with the
  soundness argument above.
- Kontrol's settings: gas off, fail-fast on (a proof stops at its first failing node), default
  iteration and depth bounds except where `runs.tsv` names them.
- solc 0.8.37 (forge's compiler inside the container, mounted read-only and pinned by sha256) and
  forge 1.5.1 inside the image (it drives the build); forge and cast 1.8.3 on the host for the
  replays and the controls. A compiler bug affects the proofs and the deployment alike.
- The mocks and harnesses: what they record and compare is what the proofs check.
- For `poseidon-frame`: Halmos 0.3.3, yices 2.6.4 and z3 4.12.6 (`requirements-halmos.txt`).
- The orchestration and the verdict extraction: `check.sh`, `scripts/` (`setup-suite.sh`,
  `kontrol-run.sh`, `kverdicts.py`, `compare.py`, `pyenv-check.py`), `mutants/make.py`, and the
  scripts of `harness/insert-loop/controls/tools/` and `harness/poseidon-frame/scripts/`. They
  select and export the source, set the build options, load the lemma and the patched `abi.md`, run
  every command, and read and accept the verdicts. A wrong script can run a proof on other inputs,
  or count a wrong verdict as expected.

## Pins

[PINS.txt](PINS.txt) holds every pin `check.sh` reads: the pocs commit `a04b8b3` and the git blob ids
of the 14 exported files (the pool source `ShieldedPool.sol` has sha256 `8cad5615...fac59c94`); the
three soldeer zips of the pinned `soldeer.lock` by sha256; zk-kit.solidity at `a171c845` and
kontrol-cheatcodes at `187b89ad` by tree id; the image digest and the Kontrol version; the sha256 of
the stock and patched `abi.md` and of the lemma file; forge, cast and solc by version and binary
sha256; for `poseidon-frame`, the Python version, the yices binary and the RECORD digest of each
package of the Halmos environment. The mutants are generated from `mutants/<suite>/*.diff` by
`mutants/make.py`, which applies each diff strictly to the exported source and requires the sha256 of `MUTANTS.sha256`.

## Re-check

Start from a checkout with the submodule:

```
git clone --recurse-submodules https://github.com/ethsystems/shielded-pool-model.git
# or, in an existing checkout:
git submodule update --init contract-kontrol/pocs
```

You need Docker (the right to run containers), bash, git, python3, curl, sha256sum, tar, patch,
forge and cast 1.8.3 and solc 0.8.37 (as [deployment/](../deployment/README.md) installs them;
`check.sh` downloads solc into `.deps/` if it finds none) and, for `poseidon-frame`, Halmos in a
Python 3.12 environment (`python3.12 -m venv .venv && .venv/bin/pip install --require-hashes
--no-deps -r requirements-halmos.txt`; or set `HALMOS`). Pull the image once:

```
docker pull runtimeverificationinc/kontrol@sha256:858f004144d61b005997f56bb8b7cd15673850286c96e0e5ec0502d9c9a9e204
```

Then:

```
cd contract-kontrol
./check.sh                                   # every suite of harness/SUITES.txt
./check.sh guards-patched insert-loop        # every run of some suites
./check.sh withdraw-success:token-above-0x11 # one prove run and its build: CHECK PARTIAL
./check.sh public-inputs:replay              # the forge replays only, no Docker: CHECK PARTIAL
# expect a RUN line per run, a CHECK line per verdict, "CHECK PASS suite <name>" per suite,
# and the last line CHECK PASS: ... (CHECK PARTIAL (...) when the selection names single runs)
```

A selection names runs of `harness/<suite>/runs.tsv`; a selected prove run brings its suite's build.
`check.sh` rejects an unknown suite or run.

In order, `check.sh`:

0. checks the selection and the inventory of every suite (`scripts/compare.py --inventory`: each
   run of `runs.tsv` has rows in `EXPECTED.tsv` and each row a run, and each mutant has an expected
   failing proof or replay);
1. checks forge, cast and solc (versions and binary sha256); when a `halmos` run is selected, checks
   the Halmos environment (`scripts/pyenv-check.py`, as in `contract-halmos`); when a build is
   selected, checks the image's repository digest, `kontrol version`, the image's `abi.md` against its pin, that
   `abi.md.diff` turns it into `kevm-patch/abi.md`, that the pinned commit of the KEVM fork holds
   that file on top of the image's `v1.0.921` (only when a selected run mounts the patched file; skipped
   with `KEVM_FETCH=0`), and the lemma file;
2. checks that `pocs/` holds `a04b8b3` and that the 14 files to export have the pinned blob ids;
3. fetches the soldeer zips by the pinned lock (checked by sha256 and soldeer's integrity hash),
   zk-kit.solidity and kontrol-cheatcodes by commit (checked by tree id), into `.deps/`;
4. for each suite: `scripts/setup-suite.sh` exports the pin with `git archive` (every file checked
   against its blob), adds the dependencies, applies the documented `foundry.toml` patch
   (`scripts/foundry-kontrol.txt` and one remapping), copies the harness and generates the mutants;
   then runs each selected row of `harness/<suite>/runs.tsv`: `build` and `prove` rows in the
   container (`scripts/kontrol-run.sh`, whose RUN end line holds the command exit and the runner
   exit), `forge` rows (replays), `controls` rows and `halmos` rows on the host (each log ends with
   its exit status, `HOST_EXIT=`);
5. reads every verdict and every failing node's output (`scripts/kverdicts.py`, from Kontrol's
   output and the saved proof graph) and compares them, and the exit status of every selected run,
   with `EXPECTED.tsv` (`scripts/compare.py`).

Each container: `--memory 8g --memory-swap 8g` (no swap), core dumps off, no network, one at a time.
Before each container `kontrol-run.sh` waits until no other Kontrol container runs and `free -g`
shows at least `GATE_GIB` (default 10) GiB available. Environment: `CAP`, `BUILD_CPUSET` (default
`0-1`), `PROVE_CPUSET` (default `0-5`), `TLIM` (seconds per container, default 7200), `GATE_GIB`, `FORGE`, `CAST`,
`SOLC`, `POCS`, `DEPS_CACHE`, `WORK`, `HALMOS`, `PULL=0`, `SOLC_FETCH=0`, `KEVM_FETCH=0`, `TOOLS_UNPINNED=1`.

The last line is `CHECK PASS` (exit 0) only when every run of every named suite ran, exited with
the status its expected verdicts give, and gave every expected verdict and failing output. A
selection that leaves runs of a suite out ends `CHECK PARTIAL (<selection>)` with exit 3, even when
everything selected matched. Anything else ends `CHECK FAIL` (exit 1; exit 2 for a usage error). A
selected run with no result, or whose log shows a timeout, a kill, a crash or another exit status
than its expected verdicts give, is void: each of its expected verdicts is a mismatch, never a
pass. `scripts/compare.py` lists the rules.

Cost, measured here (cap 8 GiB, CPUs `0-1` for a build and `0-5` for a proof run): each build 2.5
to 4 minutes at 7.3 to 7.9 GB peak (the `public-inputs` build reached 8.59 GB, just under the cap;
KEVM runs two kompiles in parallel, so a build can hit the cap and must then be rerun);
`withdraw-success` `token-above-0x11` 3,438 s and `two-tokens` 3,554 s (peaks 6.9 and 7.1 GB);
`guards-patched` 3,000 s; `guards-stock` 2,179 to 2,324 s per run; `insert-loop` `rejections`
326 s and `controls` a few seconds; `public-inputs` `canonical` 1,387 s, `order` 1,532 s and
`fixed-token` 1,543 s (peaks 7.8, 7.6 and 6.8 GB; the whole suite 4,619 s); `poseidon-frame`
about 30 s. Everything took about 6.3 hours. `work/` takes 0.5 to 2.5 GB per suite (saved proof graphs); neither `work/`
nor `.deps/` is tracked.

## Layout

- `check.sh`: the check.
- `harness/SUITES.txt`; `harness/<suite>/`: the Kontrol harness, the replays (`*Replay.t.sol`) and
  `runs.tsv` (each row: kind, run, KEVM `stock` or `patched`, command). `harness/insert-loop/`:
  `controls/` (the Foundry project of the controls) and `k/` (the K claims and `loop-funcs.k`).
- `mutants/make.py`; `mutants/<suite>/`: `MUTANTS.tsv` (id, base, diff, output, change), the diffs,
  `MUTANTS.sha256`.
- `lemmas/bytes-prefix.k`: the bytes-prefix rule.
- `kevm-patch/abi.md`, `kevm-patch/abi.md.diff`: the patched KEVM file (the copy that is mounted
  into the container; the same file as fork commit `6795265`) and its one deletion.
- `scripts/`: `setup-suite.sh`, `kontrol-run.sh`, `kverdicts.py`, `compare.py`,
  `pyenv-check.py` (as in `contract-halmos/`), `soldeer-integrity.py` (as in `deployment/`),
  `foundry-kontrol.txt`, `rename-map.txt`, and `klengths.py`, which prints the `bytes` length bounds at the test entry of saved proofs (stock:
  `<= 2^30` and `< 2^64`; patched: `< 2^64` only), to show from the graph which KEVM a run used.
- `EXPECTED.tsv`: every expected verdict (suite, run, proof, verdict, failing outputs, and the date
  of the earlier run it comes from, or "new").
- `PINS.txt`, `RESULT.md`, `pocs/` (the git submodule, ethsystems/pocs at `a04b8b3`).

## Earlier names

The proofs were first written with working names. The claim board and the records of the earlier
runs (2026-10-01, 2026-10-02, 2026-10-06 and 2026-10-07; those records are not in this repository)
use them.
[scripts/rename-map.txt](scripts/rename-map.txt) maps each earlier run label, file, contract, test,
mutant and module to its name here. Only names and comments changed. The proof bodies, the error
names (so the error selectors in `EXPECTED.tsv` equal those of the earlier runs), the mutated
lines and the prover options are those of the earlier runs, with these exceptions, each stated in
its suite's section: `guards-stock` leaves out the stalled canonical-input checks;
`guards-patched` keeps only the withdraw test contract (the deposit and transfer contracts did not
close) and adds three mutant siblings; in `withdraw-success` the probe and non-vacuity bodies moved
to a contract `WithdrawSuccessProbes` that the mutant siblings do not inherit (two builds of the
earlier layout hit the 8 GiB cap here), and `two-tokens` now runs with the bytes-prefix rule
loaded; `poseidon-frame` rebuilds the library from the pinned package with the recorded settings in
place of the earlier build inputs.

The compiler differs from the earlier Kontrol runs: they let the image's forge 1.5.1 choose solc,
and it chose 0.8.33 (Prague EVM target, from the saved build information). This package pins solc
0.8.37, the compiler of the deployment check, and keeps forge 1.5.1's Prague target (the deployment
builds for Osaka). So the bytecode under proof here is the 0.8.37 build, not the 0.8.33 build of the
earlier runs; a verdict reproduced here is a verdict about the 0.8.37 build. The archived K claims
were not reproduced (see the opening). `check.sh` requires solc
0.8.37: `SOLC` can point at another copy of it, and `TOOLS_UNPINNED=1` accepts a build of 0.8.37
whose sha256 differs from the pinned Linux x86_64 binary. Another compiler version needs other pins
in `PINS.txt`.

## Open

- `poseidon-frame` is a Halmos check; it could move to the Halmos package.
- The K claims of the insertion loop are archived, not run by `check.sh`, and have no reproduced
  proof procedure here.
- No `check.sh` invocation has yet ended `CHECK PASS` over every suite.
- The per-node feasibility evaluation of the earlier runs (every constraint of a failing node true
  at one point) is not carried; the replays are.
