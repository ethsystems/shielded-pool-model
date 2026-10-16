# Where the inputs come from

`check.sh` rebuilds the verifiers from files it reads at pinned commits. This file
says where each input comes from, what is pinned but not committed, and what the
check does not read.

## The pool files: the pocs submodule

Source: ethsystems/pocs (public, https://github.com/ethsystems/pocs), commit
`a04b8b38969dfc2ee64de47edee7e396454204a8`, directory
`pocs/private-payment/shielded-pool/`, as the git submodule `../pocs`. The commit
is pinned twice: by the superproject's submodule entry, which `git submodule
update` checks out, and by `pocs_commit` in `TOOLS.txt`, which `check.sh`
requires. The private repo ethsystems/pocs-private has the same commit; the public
master pointed at it on 2026-10-14.

`check.sh` reads 13 files of that directory as git blobs of the pinned commit
(`git cat-file blob <commit>:<path>`) and checks their sha256 against
`SHA256SUMS`: the workspace `Nargo.toml`, the three circuit packages (`Nargo.toml`,
`src/main.nr`), the test circuit member that the workspace manifest lists (nargo
refuses to load the workspace without it; the check never compiles it), the three
committed verifiers, and `scripts/generate-verifiers.sh`. `git -C pocs ls-tree
a04b8b3 <path>` gives each file's blob id.

The three verifier files are identical at `edf1b60` (the commit that regenerated
them) and at `a04b8b3`. After the pin, ethsystems/pocs-private pull request 16
(`748884e`, merged 2026-10-08) changed `circuits/transfer/src/main.nr` and
`contracts/src/verifiers/TransferVerifier.sol` (the verifier's blob there is
`2255c5084ffb0ad5a06f552d1d6f26a243a4b93b`). That commit is not in the public repo
yet. The package stays at `a04b8b3`; the newer commit is not reproduced here.

`generate-verifiers.sh` is the committed recipe. The check runs the same two bb
commands (`write_vk -t evm`, `write_solidity_verifier -k`) into its own directory,
but not the script: the script writes over the committed verifiers in place, and
its `nargo execute` step needs witness inputs that a key does not (`bb write_vk`
builds the key from the ACIR alone).

## The Noir dependencies

poseidon v0.3.0 at git `0880c371e88e583d39515fd3f877538657ac41eb` and
binary-merkle-root v0.0.2 at git `ff3070116b446ca02ad233b9ad466677d127e64e`, as
the three circuit `Nargo.toml` files name them (by git URL and tag). `DEPS.txt`
records both commits; it is byte-identical to the research record. The check
clones each tag the way nargo does (`git clone --depth 1 --branch <tag>`) and fails
if the fresh clone is at another commit; a commit already in `.deps/` is used
without asking upstream. It unpacks the pinned commit where nargo looks for it.
The trees it unpacks are equal, file for file, to the research run's nargo cache
(checked 2026-10-14).

## Pins written for this package

- `TOOLS.txt`: the pocs commit and directory, and the tool, release and CRS pins.
  The tool lines are rewritten from the research `TOOLS.txt`: the same version
  strings and sha256 values, the worker's home paths dropped, the release pages,
  assets and CRS URLs added. The asset digests are GitHub's own release digests,
  read on 2026-10-13; the research log records that unpacking those two assets
  gives binaries with the pinned sha256.
- `SHA256SUMS`: the sha256 of the 13 pool files. It does not pin `TOOLS.txt` and
  `DEPS.txt`: they are the pin files themselves, reviewed in the diff like
  `expected.json`.

## Pinned but not committed

- The CRS prefix: the first 8,388,608 bytes (131,072 G1 points) of Aztec's
  `g1.dat`, sha256 `3718ffbed583d8a279ccb2545196d5618e3fd97512b65aa051d2ebd0f57fb999`.
  Left out here for size (8 MiB); the research archive carries it as an archived
  input, with this hash. `check.sh` takes the prefix from a local bb CRS
  directory or downloads it from the Aztec CDN, and checks the hash before use. The
  largest circuit, transfer, has N = 131072, which is exactly what the prefix holds.
- The tools, by version and binary sha256 (`TOOLS.txt`).

## Not read by the check

The submodule holds the whole pocs repository. The check reads only the 13 files
above. In particular it does not read:

- `circuits/{deposit,transfer,withdraw}/Prover.toml`: keyed PoC fixtures with no
  funds (pocs `a04b8b3` says so in their comments), public in the repo, and not
  needed for a key.
- `contracts/src/ShieldedPool.sol` and the rest of the Foundry project
  (`contracts/script/`, `interfaces/`, `mocks/`, `CompositeVerifier.sol`,
  `deployments.toml`, `foundry.toml`): they matter for a check of the deployed
  contracts, not for the build reproduction.

## Earlier runs (research repo, cited)

oskarth/lean-shielded-pool, branch `dispatch/xo-fv-lean` at `1262a16`,
`evidence/2026-09-30-followup/vk-reproduction/`: `LOG.md` (the worker log),
`deliverable/scripts/` (the original `reproduce.sh` and `compare.py`),
`run-evidence/first/` and `run-evidence/fresh/` (two passing runs, 78 and 75 checks),
`EXCLUDED.txt` (the files the archive left out). The runs here, on 2026-10-13 from
copied files and on 2026-10-14 from the submodule, reproduced every value in
`expected.json`.
