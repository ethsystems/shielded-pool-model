> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-07 (amended 2026-10-11).
> Sanitised for publication: see [../README.md](../README.md).

# REPORT: deployment check (C1), 2026-10-07

> The review of this report ended with one open item, R5-RERUN: the printed replay command
> could not run as printed because `tools/replay.sh` had mode 100644. A later commit set the executable bits and the next
> ran the printed command (`replay-exec/`, RESULTS OK). Astra re-read both on 2026-10-11: modes 100755 at HEAD, the run follows the fix, `check-results.py`
> on `replay-exec/logs` returns RESULTS OK; verdict CLOSED. It also noted one prerequisite the Rerun section omitted,
> TRACE's `run/final/collected.json`; added below.

Night of 2026-10-06/07. Nothing pushed or posted.

Tags: [checked] means I ran it and the output is in the named log. [read] means I read it at the named place. `deploy-check.py`, `recheck-deploy.sh` and `soldeer-integrity.py` are copied in `scripts/` beside
this report. Other paths are relative to the research-phase directory of this report (not copied here).

## Result

`scripts/recheck.sh deploy <rpc> <addresses.json> [new-out-dir]` exists and works offline. It answers "how do you know you are running the OSS code?" for one chain snapshot, under the limits below.

- On the TRACE anvil deployment (a local test chain, 2026-10-06) it gives `VERDICT PASS`. All 12 runtime codes are byte-equal to a fresh build of ethsystems/pocs `a04b8b3`, and so are their 53-byte CBOR metadata tails. [checked] `logs/real.log`
- Each of the three planted deviations gives `VERDICT FAIL` with the named check. [checked] `logs/d1-mock.log`, `logs/d2-swap.log`, `logs/d3-byte.log`
- Four extra controls test the metadata boundary, the event check and the owner check. [checked] `logs/controls.log`
- `tools/check-results.py` reads saved logs and checks each case's exit code, FAIL names and WARN names. It does not rerun the chain. On `logs/`: `RESULTS OK`. [checked] `logs/RESULTS.txt`
- `tools/replay.sh` reran all eight cases into a new dir with fresh runs, claims and logs, then validated them: `RESULTS OK`. [checked] `replay/logs/RESULTS.txt`

| Case | Plant | Verdict | Failing checks |
|---|---|---|---|
| real | none | PASS | none |
| d1-mock | PoC `Deploy.s.sol` with `USE_MOCK_VERIFIER=true` | FAIL | MOCK, SLOTS, CODE:composite |
| d2-swap | `CompositeVerifier(transfer, deposit, withdraw)` and a pool on it | FAIL | SLOTS, CODE:composite |
| d3-byte | pool byte 3237 changed (`anvil_setCode`) | FAIL | CODE:pool only |
| c4-ipfs | pool byte 6281, inside the ipfs digest | PASS, METADATA WARN | none |
| c5-edge | pool byte 6265, last byte before the tail | FAIL | CODE:pool only |
| c6-event | owner calls `setVerifier` with the same composite | FAIL | EVENTS only |
| c7-owner | claim names a different owner | FAIL | OWNER only |

## What the target does

1. **Fresh source.** `git archive a04b8b3` of `foundry.toml`, `soldeer.lock`, `contracts/src` and `contracts/script`; every file's `git hash-object` must equal `git ls-tree a04b8b3` (16 files). [read] `recheck-deploy.sh:22-25`; [checked] `logs/real.log`
2. **Dependencies.** The three soldeer packages must match the lock's `integrity` values; `scripts/soldeer-integrity.py` reimplements that hash and reproduces all three. zk-kit comes from `git archive` of the lock rev a171c845; its tree id `7ced94ae` is logged. [read] `recheck-deploy.sh:29-34`; [checked] `logs/real.log`
3. **Offline build.** `unshare -rn forge build --offline --build-info`, in a new network namespace with no network access. 49 files, solc 0.8.37, exit 0. The checker refuses a build-info whose sources differ from the export, or whose settings are not solc 0.8.37, optimizer on, 100 runs, osaka, no via-IR. [read] `recheck-deploy.sh:38`, `deploy-check.py:58`, `:63`; [checked] `logs/real.log`
4. **Expected code.** For each contract the checker fills the rebuilt `deployedBytecode`:
   - link slots get the claimed library addresses;
   - immutables get claimed values (composite: the three verifier addresses) or source values (Honk verifiers: `N`, `LOG_N`, `VK_HASH`, `NUMBER_OF_PUBLIC_INPUTS`, `$MSMSize` from its constructor line);
   - a library's call-protection prefix gets its own claimed address.
   No byte is masked. An unknown link or immutable, or a wrong width, gives FAIL. [read] `deploy-check.py:140-168`
5. **Compare.** The two-byte suffix gives the CBOR length L. The tail must decode as a pure metadata map. The checker cuts exactly L+2 bytes from each side, then compares the bodies byte for byte (CODE) and the tails byte for byte (METADATA). A tail difference with the same solc is a WARN, never hidden. [read] `deploy-check.py:174-211`, `:257`
6. **Configuration**, read only from the RPC at the claimed block [read] `deploy-check.py:226-360`:
   - SLOTS: each composite getter returns the claimed role address, and that code holds the role's `VK_HASH` at the `$VK_HASH` offset.
   - MOCK: no slot and not `pool.verifier()` equals the rebuilt MockVerifier code.
   - WIRING: the pool points to the claimed composite and registry.
   - EVENTS: zero `VerifierUpdated` logs from block 0 to the claimed block.
   - OWNER: `owner()` and the OwnershipTransferred history.
   - TOKENS: the set replayed from TokenAdded/TokenRemoved logs equals the claimed list; `supportedTokens` is true for each.
   - CHAIN and CHAIN-END: chain id, head and block hash at start and end.

The 12 contracts: pool, composite, registry, three Honk verifiers, their three `ZKTranscriptLib` libraries, LeanIMT, PoseidonT3, PoseidonT5. The libraries beyond C1's list are linked by the verifiers and the registry. [read] `claims/real.json`; TRACE broadcast library lists

## How the tests were made

- **Deployment under test.** TRACE's saved anvil state (sha256 `b2609e81`) loads into a fresh anvil on 127.0.0.1:8646 per case; an occupied port is refused. Before any plant, code keccak at the pool, composite and withdraw verifier must equal TRACE's `collected.json`, and the withdraw tx must sit in block 15. All equal in every case. [read] `tools/run-all.sh:22-47`; [checked] `STATE` lines in each log
- **Claims.** `claims/real.json` takes addresses from TRACE's `deployments.toml` and broadcast library lists. Each case keeps the intended verifier roles and applies only its stated fixture change: new pool, composite, registry and library addresses (D1, D2), or a different owner (C7). Block number and hash come from the planted head. [read] `tools/run-all.sh:58`, `:116`, `:125`, `:135`
- **Fixtures.** D1 and D2 are built in a separate export, never a run's reference dir. [read] `tools/run-all.sh:91`
- **Caps.** Anvil 2 GiB, each recheck 4 GiB (`MemorySwapMax=512M`). [read] `tools/run-all.sh:23`, `:66`

## Deviation details

- **d1-mock.** The claim keeps the real verifier addresses. MOCK names all three slots as MockVerifier. SLOTS says the VK_HASH word is absent (343-byte code). CODE:composite differs at byte 157: claimed deposit verifier address against the mock address. [checked] `logs/d1-mock.log`
- **d2-swap.** The claim keeps the true roles. SLOTS says the deposit slot holds the transfer `VK_HASH`, and the reverse. CODE:composite differs at byte 157. METADATA:pool is a WARN: `forge create --libraries` puts the library address into the solc settings. A `forge build --libraries` of the same export gives the chain's ipfs hash `12208d17`; CODE:pool PASSes. [checked] `logs/d2-swap.log`, `logs/d2-metadata-cause.log`
- **d3-byte.** Byte 3237 is the last byte of the `TokenNotSupported()` selector, used only by `removeSupportedToken`. CODE:pool reports "first difference at byte 3237"; every other check PASSes. [checked] `logs/d3-byte.log`

## How each judge item is handled

- **Sources from the deployment's own `out/`.** Every reference is a fresh `git archive` built in the run's own out dir; a build-info with other source text is refused. TRACE gave only addresses, the state and its provenance hashes. [read] `deploy-check.py:58`; [checked] `logs/real.log`
- **Strip that hides differences.** Links, immutables and the library prefix are filled, not masked. The cut is exactly the tail the suffix names: c5 (last body byte) FAILs, c4 (tail byte) WARNs. [checked] `logs/controls.log`
- **PASS without deviations.** Real and deviation runs used the same code: one driver hash in every `logs/` header, and one in every `replay/logs/` header. [checked] `logs/CODE-SHA256.txt`, `replay/CODE-SHA256.txt`
- **FAIL for an unrelated reason.** Every case has CHAIN and CHAIN-END PASS and no traceback; d3, c5, c6 and c7 fail only at the planted check. [checked] `logs/RESULTS.txt`
- **Rebuild compared with itself.** Chain bytes come only from `eth_getCode`; d3 and c5 show a one-byte chain change is found. [checked]

## Limits

- One local snapshot, not a public chain. The RPC and its history are trusted. No deployment outside a local test chain exists. [read] CLAIM1.md:151
- The check binds code and configuration at one block. It says nothing about later owners, token honesty (A10) or owner calls in token callbacks (A13). [read] CLAIM1.md:151
- Mock-off means: slots hold the rebuilt Honk code with the right `VK_HASH`, and no slot equals a rebuilt mock. No on-chain flag exists. [read] a04b8b3 `contracts/script/Deploy.s.sol:21-31`
- forge 1.8.3, solc 0.8.37 and anvil are trusted; a shared compiler bug affects both sides. [read]
- zk-kit provenance is the direct `git archive` of the lock rev; the tree id is recorded, not recomputed after extraction. [read] `recheck-deploy.sh:33`
- `logs/` headers say "driver working tree differs" because those runs wrote tracked log files. The replay writes no tracked file, and its headers have no such line. [checked] `replay/logs/*.log`
- An early commit message says 13 runtime codes; the right count is 12. The round 2 plan had 1,502 words, two over its cap. [read]

## Generated files, not committed

`.deploy-work/` (ignored), 2.3 GB [checked] `du -sh`: `runs/` and `replay-1/` (export, dependencies and build per case), `chain/` (TRACE state copy), `deps/`, `fixture/`, `libcheck/` (d2 metadata build), `ref/`, `bi/`, `logs/` (smoke builds).

## Rerun

From the repo root, with forge/cast/anvil 1.8.3, solc 0.8.37, port 8646 free, the state copy in `.deploy-work/chain/`, TRACE's `run/final/collected.json` where `tools/run-all.sh:10` and `:36` expect it, verified packages in `.deploy-work/deps/`, and `POCS`/`ZKKIT_GIT` as set in `tools/run-all.sh`:

```
tools/replay.sh <new-dir>   # in the research-phase directory; not copied here
```

It writes runs, claims and logs only under `<new-dir>` and ends with `check-results.py` on those logs. A single `scripts/recheck.sh deploy <rpc> <claim>` needs a running RPC and `POCS`, `SOLDEER_DEPS`, `ZKKIT_GIT`.
