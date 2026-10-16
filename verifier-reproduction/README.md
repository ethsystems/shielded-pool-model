# verifier-reproduction: the committed Solidity verifiers rebuilt from the circuits

The three Solidity verifier contracts committed at `a04b8b3` of ethsystems/pocs
(public; ethsystems/pocs-private has the same commit) under
`pocs/private-payment/shielded-pool/contracts/src/verifiers/` are
the files that Barretenberg generates from the three Noir circuits committed at the
same revision, byte for byte, and the verification-key hash that bb computes for
each circuit equals the `VK_HASH` constant in the committed file. The tools are
nargo 1.0.0-beta.21 and bb 5.0.0-nightly.20260324. This is a build reproduction:
`check.sh` reads the circuit sources and the committed verifiers from the pocs
repository itself (the git submodule `pocs/`, pinned at `a04b8b3`), compiles the
circuits, generates the keys and verifiers with bb, and compares the bytes. This
package carries no copy of pocs files. It is not a Lean theorem, it imports
nothing from the model, and the model gate (`scripts/gate.sh`) never runs it.
Nothing here changes the claim in the parent README.

## What the check says, and what it does not

The check establishes one thing: the committed verifier sources at `a04b8b3` are
bb's output for exactly these circuits, so a change to a circuit, to a key, or to a
verifier file would show up as a byte difference (the self-test plants such
changes). Everything below is open, and the package claims none of it.

- The pin is not the latest circuit. ethsystems/pocs-private pull request 16
  (`748884e`, merged 2026-10-08) changed `circuits/transfer/src/main.nr` and
  `TransferVerifier.sol` after `a04b8b3`. The package stays at the pin. Moving it
  is a submodule bump plus new pins (`inputs/TOOLS.txt`, `inputs/SHA256SUMS`,
  `expected.json`) once that commit is public; it is not covered here.
- Proof-system soundness. Whether a proof the verifier accepts implies a satisfying
  witness is the cryptographic floor. The check says nothing about it.
- Deployed bytecode identity. Whether any deployed contract is compiled from these
  sources needs a check of the deployed bytecode, not this package. `VK_HASH` is an
  internal immutable with no getter, so an on-chain check must compare runtime
  bytecode; nothing here does.
- The pool contract. Nothing about `ShieldedPool.sol`, how it orders or passes the
  public inputs, or which verifier address it calls.
- Compiler and translator faithfulness. The check compares bb's output with bb's
  earlier output. It does not check that the ACIR nargo emits means what the Noir
  source says, nor that bb's key and verifier are a correct UltraHonk verifier for
  that ACIR.
- The pinned tools. Stable bb 5.0.0 cannot decode these beta.21 artifacts (it stops
  with "error converting into field Circuit::opcodes", recorded in the research run),
  so only the nightly reproduces the files. That is a pin, not a statement about
  either build's correctness.

The package never says "the verifier is correct". It says "the committed verifier
files are the build of these circuits with these tools".

## Trust base

- nargo 1.0.0-beta.21 (noirc git `89a0f0fa`), binary sha256
  `0852cd5631ac5ca25f744f25c931e3cff16351d9bcdbfb03cebb48a4494a0fe3`.
- bb 5.0.0-nightly.20260324, binary sha256
  `d7621dfb151f55c23fb04bf274f366a6a1e0516b85a3cf0ae9165a9952509793`.
  Both pins are the Linux x86_64 release assets (`inputs/TOOLS.txt` names them).
  `check.sh` fails closed on another version. Another build of the same version
  (for example macOS) needs `TOOLS_UNPINNED=1`, and the PASS line then says so.
- The CRS: the first 8,388,608 bytes of Aztec's BN254 `g1.dat`, sha256
  `3718ffbed583d8a279ccb2545196d5618e3fd97512b65aa051d2ebd0f57fb999`. It is not
  committed (8 MiB). The check takes that prefix from an existing bb CRS directory
  (`~/.bb-crs`, or `CRS_DIR`), otherwise downloads it from the two Aztec URLs in
  `inputs/TOOLS.txt`, and checks the hash before bb sees it. `CRS_FETCH=0` forbids
  the download.
- The pool sources: ethsystems/pocs at commit
  `a04b8b38969dfc2ee64de47edee7e396454204a8`, as the submodule `pocs/`. The check
  requires the submodule to be checked out at that commit (`pocs_commit` in
  `inputs/TOOLS.txt`), reads the 13 files it needs as git blobs of that commit, not
  from the working tree, and checks each against its sha256 in `inputs/SHA256SUMS`
  before the build.
- The two Noir dependencies, poseidon v0.3.0 (git `0880c371`) and binary-merkle-root
  v0.0.2 (git `ff307011`), as the circuits' `Nargo.toml` files name them (by git URL
  and tag). The check makes the same shallow clone of each tag that nargo makes and
  requires the commit in `inputs/DEPS.txt`, so a fresh clone of a tag that has moved
  fails. The clones stay in `.deps/` (or `DEPS_CACHE`), keyed by commit; a commit
  already there is used without asking upstream. The check places each tree where
  nargo looks for it and stops if a pinned `Nargo.toml` names a git dependency that
  `inputs/DEPS.txt` does not pin. nargo runs with `GIT_ALLOW_PROTOCOL=none`, so if
  nargo tries to fetch anything itself, git refuses and the build fails.
- bash, git, python3 (for the ACIR hash, `expected.json` and the self-test edits), GNU
  coreutils (`sha256sum`, `od`), diffutils (`cmp`, `diff`), findutils (`xargs`, in
  the self-test), grep, sed, tar, and curl
  (for the tool downloads, and for the CRS when it is not on the machine). macOS needs
  coreutils installed for `sha256sum`.

## Inputs

The 13 pool files are read from `pocs/` at `a04b8b3`, under
`pocs/private-payment/shielded-pool/`. The key ones:

| File | sha256 |
|---|---|
| `circuits/deposit/src/main.nr` | 7d1b3c3347415023fe2e7e193663f28beaf3a042d0628b04d64bbcc8aa515391 |
| `circuits/transfer/src/main.nr` | 33ab018365efdc2107ae31bba10978ee878bf316c6bf4d51de777c0c9b1b8cfd |
| `circuits/withdraw/src/main.nr` | a987c5ba151a9dafa03ff3cc3082a210f2ab098a89d0f89b4a87b5addf84b974 |
| `contracts/src/verifiers/DepositVerifier.sol` | f0157867373f50a2057313c5243e808258b508f182cba91421bbd4d26d21aeed |
| `contracts/src/verifiers/TransferVerifier.sol` | 33ee420f3ac09993c09e7cef00fa564fc8fa56c1b71eee0ffa92e791c7b2f895 |
| `contracts/src/verifiers/WithdrawVerifier.sol` | 2e769a992a63eea8ee150144703db3e2b3109250d95ffff66db4b1384edfc3d2 |
| CRS prefix (not committed) | 3718ffbed583d8a279ccb2545196d5618e3fd97512b65aa051d2ebd0f57fb999 |

`inputs/SHA256SUMS` pins all 13, the three `Nargo.toml` package manifests, the
workspace manifest, the test circuit member it requires and the committed
generation script included. `expected.json` pins, per circuit, the ACIR sha256, the
binary key sha256, the key hash and the verifier sha256, plus the key hash, ACIR
and verifier of one planted mutant (withdraw with a 127-bit amount range) that the
self-test must reproduce. The committed `VK_HASH` values:

| Circuit | `VK_HASH` | N | public inputs |
|---|---|---|---|
| deposit | 0x21cba1cbaf0dfc979b5978d694f7c2bedf98ef8012139a33e3218132e642230d | 32768 | 14 |
| transfer | 0x0ff59d91add8bc788eec2e2900e4ec1a9a726bb135c268842be11ab45a5eeb4d | 131072 | 14 |
| withdraw | 0x0c9e8ed785da4796fe241839bab23899dd7a4dc2723faa4db3b9fbd9e6183cfc | 65536 | 13 |

## Re-check

Start from a checkout of this repo with the submodule:

```
git clone --recurse-submodules git@github.com:ethsystems/shielded-pool-model.git
# or, in an existing checkout:
git submodule update --init verifier-reproduction/pocs
```

Install the two pinned tools anywhere; the release pages and the exact assets are in
`inputs/TOOLS.txt`. On Linux x86_64:

```
curl -L -o nargo.tar.gz https://github.com/noir-lang/noir/releases/download/v1.0.0-beta.21/nargo-x86_64-unknown-linux-gnu.tar.gz
curl -L -o bb.tar.gz https://github.com/AztecProtocol/aztec-packages/releases/download/v5.0.0-nightly.20260324/barretenberg-amd64-linux.tar.gz
sha256sum nargo.tar.gz bb.tar.gz   # ed7b06fb52728ea6..., 7875a7a82c232884...
mkdir -p tools && tar -C tools -xzf nargo.tar.gz && tar -C tools -xzf bb.tar.gz
export NARGO="$PWD/tools/nargo" BB="$PWD/tools/bb"
```

Then:

```
cd verifier-reproduction
./check.sh               # expect the last line: CHECK PASS: 3 verifiers byte-identical, 3 key hashes equal VK_HASH, <n>s
./check.sh --self-test   # expect the last line: SELF-TEST PASS: 8 copies, <n>s
```

Without `NARGO` and `BB` the script takes `nargo` and `bb` from `PATH`. Relative
paths in `NARGO`, `BB`, `POCS`, `DEPS_CACHE` and `CRS_DIR` are taken from the
caller's directory. The work directory is always `work/` in this package. In order,
`check.sh`:

1. checks that nargo and bb exist, report the pinned versions (nargo also the pinned
   noirc git hash) and have the pinned sha256; on any miss it prints the release
   pages, assets and hashes and stops before anything is built;
2. checks that `pocs/` is checked out at `pocs_commit`, and writes the 13 files
   listed in `inputs/SHA256SUMS` from that commit's git objects into `work/pool`;
3. checks each of them against `inputs/SHA256SUMS`;
4. obtains each Noir dependency at its pinned commit (from `.deps/`, or a shallow
   clone of its tag) and unpacks it into a private `HOME` under `work/`, then checks
   that every git dependency in the pinned manifests is among them;
5. obtains the CRS prefix as described above and checks its hash;
6. for each circuit runs `nargo compile --package`, `bb write_vk -t evm` and
   `bb write_solidity_verifier`; compares the generated `.sol` with the committed
   file byte for byte (`cmp`), printing the first difference on a miss; compares
   bb's `vk_hash` output with the `VK_HASH` constant of the committed file; and
   compares the ACIR, key, key hash and verifier hashes with `expected.json`;
7. prints `CHECK PASS` only if every step passed. The measured values land in
   `work/results.txt`.

The build needs no network once the submodule, `.deps/` and the CRS are on the
machine. Only nargo's git fetches are blocked; the clones and the CRS download in
steps 4 and 5 use the network when their files are not on the machine.

`--self-test` copies `check.sh`, `expected.json` and `inputs/` eight times, gives
each copy its own clone of `pocs/` at the pin, plants seven changes, and runs the
check on each copy. Each plant must fail at its stage, and the output must show
its exact reason: pocs checked out at another commit must fail at the source
gate; a committed verifier edited and the pin moved to that commit, without
updating the hashes, must fail at the input gate on `DepositVerifier.sol`; a
committed `VK_HASH` digit flipped (pin and hashes updated) must fail at the byte
comparison of `TransferVerifier.sol`; the withdraw circuit narrowed to a 127-bit
amount range (pin and hashes updated) must fail at the byte comparison of
`WithdrawVerifier.sol` and must reproduce the recorded mutant ACIR, key hash and
verifier; a poseidon tag that moved upstream (a local repository stands in for
github.com, with an empty cache) must fail at the dependency gate; a dependency
that a pinned manifest names but `inputs/DEPS.txt` does not pin must fail at the
dependency gate; a bb that reports version 5.0.0 must fail at the version check
before any build (run with `TOOLS_UNPINNED=1`, so the checksum check cannot be the
reason). The unchanged copy must pass.

Cost on a Linux laptop (xps26, 16 threads, btrfs), measured 2026-10-14:
`git submodule update --init verifier-reproduction/pocs` 1.7 s and 3.7 MB;
`check.sh` 9 s with the CRS from `~/.bb-crs` and the dependencies in `.deps/`,
10 to 11 s when it clones the dependencies; `--self-test` 31 s. bb reports a peak
of 116 MiB for the transfer key. `work/` takes 16 MB and `.deps/` 3.6 MB; neither
is tracked.

## Files

- `check.sh`: the check and the self-test.
- `expected.json`: the expected hashes. It is the reviewed output of the research run,
  and every run here reproduced every value.
- `pocs/`: the git submodule, ethsystems/pocs at `a04b8b3`.
- `inputs/TOOLS.txt`: the pocs commit, the tool, CRS and release pins that
  `check.sh` reads.
- `inputs/SHA256SUMS`: the sha256 of the 13 pool files the check reads.
- `inputs/DEPS.txt`: the two Noir dependencies, their tags and commits.
- `inputs/PROVENANCE.md`: where each input comes from and what the check does not
  read.

## Where it comes from

The reproduction was first run in the research repo (oskarth/lean-shielded-pool,
branch `dispatch/xo-fv-lean` at `1262a16`,
`evidence/2026-09-30-followup/vk-reproduction/`) on 2026-09-30, twice: once with the
committed `generate-verifiers.sh` unmodified and once step by step, with the same
result, plus a fresh-copy rerun; an earlier run by another worker had been judged by
a cross-family reviewer (PASS-WITH-CORRECTIONS). Its claim table (`CLAIM1.md`, row
S3) records the result as "Proved (exact rebuild)" with the same limits as above.
The research check also matched the 28 key points in each `.sol` to their slots in
the binary key; the byte comparison here subsumes that. `expected.json` carries the
research values, and `check.sh` is a rewrite of the research scripts, with the
self-test in place of the research run's planted controls.
