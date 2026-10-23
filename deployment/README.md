# deployment: the Sepolia shielded pool against a fresh build of `a04b8b3`

At Sepolia block 11949456 (hash `0xe2adfa5f…91ea60`), the runtime code at each of the 12
claimed addresses equals the matching contract of a fresh offline build of ethsystems/pocs
(public) at `a04b8b3`, byte for byte, with links and immutables filled and nothing masked. The
metadata tails are equal too. At the same block, the three composite verifier slots hold the
claimed Honk verifiers with their own `VK_HASH`, no slot and not `pool.verifier()` holds mock
verifier code, the pool points at the claimed composite and registry, the pool emitted no
`VerifierUpdated` log, its owner and ownership history match the claim, and its token set is
the claimed one (empty). The same holds at block 11976486, a finalized block of 2026-10-23.
[RESULT.md](RESULT.md) records both runs.

`check.sh` reads the pool sources from the pocs repository itself (the git submodule `pocs/`,
pinned at `a04b8b3`), fetches the four Solidity dependencies by hash, builds offline in a
network namespace, and compares the build with the chain through an RPC. This is a deployment
check of one chain at one block. It is not a Lean theorem, it imports nothing from the model,
and the model gate (`scripts/gate.sh`) never runs it. Nothing here changes the claim in the
parent README.

## What the check says, and what it does not

The check establishes one thing: at the claimed block, the claimed addresses hold the code
that forge 1.8.3 and solc 0.8.37 build from `a04b8b3`, wired as the claim says. A different
contract, a changed byte, a swapped verifier, a mock verifier, a later `setVerifier` call, a
new owner or an added token would show up as a FAIL (the controls plant such changes in the
claim; RESULT.md lists them). Everything below is open, and the package claims none of it.

- Later blocks. The check binds code and configuration at the claimed block only. A
  `setVerifier`, `transferOwnership` or token change after it shows only if the check runs
  again at a later block.
- Token behaviour. Nothing about the tokens the pool may later support, their transfers or
  their callbacks.
- Owner behaviour. The check names the owner; it says nothing about what the owner key does.
- Verifier and proof-system soundness. SLOTS shows that each slot holds the rebuilt verifier
  for its circuit; [verifier-reproduction/](../verifier-reproduction/README.md) shows that
  those verifiers are bb's output for the committed circuits. Neither says that an accepted
  proof implies a satisfying witness.
- Correctness of the contracts. The rebuild is compared with the chain, not with the spec or
  the model. A bug in `ShieldedPool.sol` at `a04b8b3` is on the chain too.
- The thirteenth contract. The deployment also created a `MockERC20` at
  `0x9fce6bce03f3966b67da5f666d7ac0db1ba37e75` (block 11948555). It is not in the claim and
  the check does not compare its code. TOKENS finds no `TokenAdded` log, and at `a04b8b3`
  only `addSupportedToken` sets a token and emits that log, so the pool supports no token,
  the mock included.
- The RPC. Chain bytes, calls and logs come from the RPC, and the check trusts the RPC and
  its history. Running the claim on a second RPC, as RESULT.md does, narrows that trust; it
  does not remove it.

The package never says "the deployment is correct". It says "the deployed code is the build
of these sources with these tools, configured as claimed, at this block".

## What is compared

For each of the 12 contracts, `scripts/deploy-check.py` takes the rebuilt `deployedBytecode`
and fills in what the deployment decides: link slots with the claimed library addresses,
immutables with claimed values (the composite's three verifier addresses) or source values
(each Honk verifier's `N`, `LOG_N`, `VK_HASH`, `NUMBER_OF_PUBLIC_INPUTS` and `$MSMSize`), and a
library's call-protection prefix with its own claimed address. No byte is masked; an unknown
link or immutable is a FAIL. The two-byte suffix names the length of the CBOR metadata tail;
the check cuts exactly that tail from both sides, compares the bodies (CODE) and the tails
(METADATA). A tail difference with the same solc is a WARN, never hidden: a deployment whose
compiler settings carry library addresses (`forge create --libraries`) gives that WARN on the
pool. The rest is read from the RPC at the claimed block: SLOTS, MOCK, WIRING, EVENTS, OWNER,
TOKENS, and CHAIN and CHAIN-END (chain id and block hash, at the start and at the end).

The 12 contracts and the block in which each was created, measured by `eth_getCode` at
consecutive blocks:

| Claim key | Contract | Address | Created in block |
|---|---|---|---|
| `depositTranscriptLib` | `ZKTranscriptLib` (DepositVerifier.sol) | `0x3cba008e48a098017a4b331f514d5b83a16cdeac` | 11948523 |
| `withdrawTranscriptLib` | `ZKTranscriptLib` (WithdrawVerifier.sol) | `0x7cd19aac2cc4491568c93609ad50ba9bb675f48a` | 11948524 |
| `transferTranscriptLib` | `ZKTranscriptLib` (TransferVerifier.sol) | `0x5045ed70c25d12da730f11a0f6d80249ebca152b` | 11948527 |
| `depositVerifier` | `HonkVerifier` (DepositVerifier.sol) | `0x8f43176beb45505c0b80e0b115f91a1e7b1113fc` | 11948530 |
| `transferVerifier` | `HonkVerifier` (TransferVerifier.sol) | `0x0283b13dc7af959449d8344de3caa6c0deeb90ff` | 11948533 |
| `withdrawVerifier` | `HonkVerifier` (WithdrawVerifier.sol) | `0xfe5811d3a1918553027f428f56d427fb28c9def6` | 11948535 |
| `leanIMT` | `LeanIMT` (zk-kit) | `0x38b16dae55fefb3198b470e6559f76560c0cce19` | 11948547 |
| `poseidonT5` | `PoseidonT5` (poseidon-solidity) | `0x889010cdd13ee425bd7246e05fe872183b3cc39f` | 11948548 |
| `registry` | `AttestationRegistry` | `0xe64018ba103846d7b09b3cb2a8ac06384196b0ba` | 11948549 |
| `composite` | `CompositeVerifier` | `0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548` | 11948551 |
| `pool` | `ShieldedPool` | `0xabefb40982e399f979cfdc712e57e334ea2b10ea` | 11948552 |
| `poseidonT3` | `PoseidonT3` (poseidon-solidity) | `0x72b98a5fff1dd0e7001a6327b5b99d256ebd1ce8` | 11949456 |

Not in the claim: `MockERC20` at `0x9fce6bce03f3966b67da5f666d7ac0db1ba37e75`, block 11948555.
The owner is `0x53d475a7232cfaf06ff6b63c1b62b689b4db3906`; the pool's only log up to
block 11976486 is its `OwnershipTransferred` from zero to that address, in block 11948552.

### Why the event check starts at block 11948523

EVENTS, OWNER and TOKENS replay the pool's logs. Public RPCs cap the block range of
`eth_getLogs`, so both claims name `logsFromBlock` 11948523, the block of the first
deployment transaction, and the check reads the logs from there in windows of `LOG_WINDOW`
blocks. Starting there loses nothing only if the pool had no code before it, so the check
also requires empty pool code at block 11948522 and fails EVENTS otherwise. The pool was
created in block 11948552 by a contract-creation transaction of the owner account, nonce 11
(tx `0x74efa8e845b9261de2425eaccfb5e0ab4c8ef24832cbe49d3d4297b645f88621`), so its address
derives from that account and nonce, and no earlier contract can have used it. A claim without `logsFromBlock` reads the logs
from block 0 in one query, as the check first did on a local test chain.

## Trust base

- forge and cast 1.8.3 (commit `cae51ad4`), binary sha256 `deb412a7…` and `1412cb23…`, the
  Linux x86_64 binaries of the foundry v1.8.3 release asset
  `foundry_v1.8.3_linux_amd64.tar.gz` (sha256 `7ca48e6c…`; `PINS.txt` has the full values).
  forge builds the reference; cast computes the event topic hashes.
- solc 0.8.37+commit.f401782d, binary sha256 `5de843c2…`, the Linux amd64 build that
  binaries.soliditylang.org lists with that hash. forge uses exactly this binary (`--use`).
  A compiler bug shared by the deployment's build and this one affects both sides alike.
- `check.sh` fails closed on another version. Another build of the same version (for example
  macOS) needs `TOOLS_UNPINNED=1`, and the last line then says so.
- The RPC, for chain bytes, calls, logs and the block hash. `check.sh` takes any URL; RESULT.md
  names the three that were tried and what each serves.
- The pool sources: ethsystems/pocs at `a04b8b38969dfc2ee64de47edee7e396454204a8`, as the
  submodule `pocs/`. `scripts/recheck-deploy.sh` exports `foundry.toml`, `soldeer.lock`,
  `contracts/src` and `contracts/script` of `pocs/private-payment/shielded-pool/` with
  `git archive` of that commit, never from the working tree, and requires every exported file
  to hash to its blob in `git ls-tree`. `check.sh` first requires those 16 blob ids to equal
  the `blob` lines of `PINS.txt`. `deploy-check.py` refuses a build-info whose sources differ
  from the export, or whose settings are not solc 0.8.37, optimizer on with 100 runs, osaka,
  no via-IR.
- The Solidity dependencies, as the pinned `soldeer.lock` names them: forge-std 1.14.0,
  poseidon-solidity 0.0.5 and @openzeppelin-contracts 5.6.0-rc.1 as zips from the lock's URLs,
  and zk-kit.solidity at git `a171c845`. Each zip must have the sha256 of `PINS.txt`, which is
  also the lock's `checksum`; after unpacking, `scripts/soldeer-integrity.py` recomputes
  soldeer's folder hash and requires the lock's `integrity` value. zk-kit is fetched by commit,
  and its tree id must be `7ced94ae…` (`PINS.txt`). soldeer itself is not run.
- The build runs as `unshare -rn forge build --offline`, in a new network namespace with no
  network. Where `unshare -rn` is not permitted, `NO_NETNS=1` runs `forge build --offline`
  without the namespace, and the build line says so.
- bash, git, python3, curl, GNU coreutils (`sha256sum`), diffutils (`cmp`, `diff`), tar,
  grep, sed, awk, and `unshare` (util-linux) for the namespace.

## Re-check

Start from a checkout of this repo with the submodule:

```
git clone --recurse-submodules https://github.com/ethsystems/shielded-pool-model.git
# or, in an existing checkout:
git submodule update --init deployment/pocs
```

Install forge and cast 1.8.3 anywhere. On Linux x86_64:

```
curl -L -o foundry.tar.gz https://github.com/foundry-rs/foundry/releases/download/v1.8.3/foundry_v1.8.3_linux_amd64.tar.gz
sha256sum foundry.tar.gz   # 7ca48e6ca3cac1bc...
mkdir -p tools && tar -C tools -xzf foundry.tar.gz
export FORGE="$PWD/tools/forge" CAST="$PWD/tools/cast"
```

Then, with an RPC that serves state at the claimed block (an archive node):

```
cd deployment
./check.sh https://sepolia.gateway.tenderly.co claims/sepolia.json
# expect the line: VERDICT PASS failing=[] warnings=[]
LOG_WINDOW=100 ./check.sh https://sepolia.drpc.org claims/sepolia.json
./check.sh https://sepolia.gateway.tenderly.co claims/sepolia-2026-10-23.json
./check.sh --controls https://sepolia.gateway.tenderly.co claims/sepolia.json
# expect the last line: CONTROLS PASS: 7 claims, <n>s
```

Without `FORGE` and `CAST` the script takes them from `PATH`. solc comes from `SOLC`, else
from an svm copy (`~/.svm` or `~/.local/share/svm`), else `check.sh` downloads it into
`.deps/` and checks its hash (`SOLC_FETCH=0` forbids that). Relative paths in `FORGE`, `CAST`,
`SOLC`, `POCS` and `DEPS_CACHE` are taken from the caller's directory. The work directory is
`work/<claim name>/` in this package, or the third argument, which must not exist. In order,
`check.sh`:

1. checks that forge and cast report version 1.8.3 at the pinned commit and that forge,
   cast and solc have the pinned sha256; on a miss it prints the release asset and stops
   before anything is built;
2. checks that `pocs/` holds `a04b8b3` and that the 16 files to export have the pinned blob
   ids;
3. reads `soldeer.lock` at the pin, downloads each zip it names unless `.deps/` (or
   `DEPS_CACHE`) has it by sha256, checks the sha256 against `PINS.txt` and the lock, and
   unpacks it; fetches zk-kit.solidity at the lock rev unless `.deps/` has that commit, and
   checks its tree id;
4. runs `scripts/recheck-deploy.sh`: the `git archive` export and its blob check, the
   integrity check, the offline build, and `scripts/deploy-check.py`, which prints one
   `CHECK` line per check and the `VERDICT` line.

Exit 0 means `VERDICT PASS`. Any FAIL, and any RPC error, gives exit 1; an RPC error stops
the comparison with no verdict, never with a PASS. `deploy-check.py` retries HTTP 429 and
5xx answers five times.

`--controls` runs the given claim unchanged, which must pass, then planted copies of it in
`work/controls/`: a wrong registry address, the deposit and transfer verifiers swapped, a
wrong owner, an extra token, a wrong block hash, and (when the claim names
`logsFromBlock`) logs that start after the pool's creation. Each must fail at exactly its
named checks, with exactly its named warnings. The chain, the source and the build are
those of the unchanged run.

Cost on a Linux laptop (16 threads, btrfs), measured 2026-10-23: `check.sh` 9 to 13 s at
either block on Tenderly, 11 s at block 11949456 and 43 s at block 11976486 on drpc
(`LOG_WINDOW=100`, 280 log queries); `--controls` 65 to 71 s. The build takes about 3 s.
`work/` takes 134 MB per claim and `.deps/` 2 MB; neither is tracked.

## Files

- `check.sh`: the check and the controls.
- `scripts/recheck-deploy.sh`: export, dependency integrity, offline build, then the comparison.
- `scripts/deploy-check.py`: the comparison with the chain.
- `scripts/soldeer-integrity.py`: soldeer's folder hash, against the lock's `integrity`.
- `PINS.txt`: the pocs commit, the 16 blob ids, the zip sha256 values, the zk-kit commit and
  tree, and the tool versions, hashes and downloads that `check.sh` reads.
- `claims/sepolia.json`: the claim at block 11949456. `claims/sepolia-2026-10-23.json`: the
  same addresses at block 11976486.
- `RESULT.md`: the runs of 2026-10-23, with every CHECK line and the controls.
- `pocs/`: the git submodule, ethsystems/pocs at `a04b8b3`.

A claim file holds `chainId`, `block`, `blockHash`, the 12 address keys of the table above,
`owner`, `supportedTokens`, and optionally `logsFromBlock`. `deploy-check.py` ignores other
keys, such as `comment`.

## Where it comes from

The three scripts were first written and run on 2026-10-07 against a local test chain; the
frozen report and the copies are in
[evidence/2026-10-07-deploy-check/](../evidence/2026-10-07-deploy-check/REPORT.md). The
scripts here start from those copies (the first commit of this package adds them unchanged).
The changes are for a public chain and for running from this package: CHAIN and CHAIN-END
accept a chain head above the claimed block, the pool logs can start at `logsFromBlock` in
windows with the guard above, RPC calls send their own user-agent and retry rate limits, forge
uses the checked solc binary, `NO_NETNS=1` replaces the namespace where it is not permitted,
and a failed build prints its log tail. The comparison itself is unchanged.

The writeup reports a Sepolia run of this check on 2026-10-19 at block 11949456 with a PASS.
This package reproduces that verdict at that block from public inputs (RESULT.md).
