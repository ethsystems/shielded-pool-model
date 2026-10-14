# Where the inputs come from

`check.sh` rebuilds the inputs on every run: it compiles the three Noir circuits from the
pinned pocs commit, prints their ACIR and solves the committed `Prover.toml`, then compares
each output with its pinned hash in `expected.json` before it uses it. The package commits
the pins, not the outputs. The outputs go to `build/inputs/` and are not tracked.

## Pins

- `TOOLS.txt`: the pocs repository, commit and directory, and the two tools.
- `SHA256SUMS`: the 12 pocs files that the build reads, by sha256. `check.sh` reads them from
  the pinned commit as git blobs, not from the working tree of `pocs/`.
- `DEPS.txt`: the two Noir libraries, one line each: the path where nargo looks for it, the
  commit and the tag.

## Sources

- Circuits: ethsystems/pocs (https://github.com/ethsystems/pocs) at
  `a04b8b38969dfc2ee64de47edee7e396454204a8`, as the git submodule `pocs/`, directory
  `pocs/private-payment/shielded-pool`: the workspace `Nargo.toml`, and per circuit
  (`circuits/{deposit,withdraw,transfer}`) `Nargo.toml`, `src/main.nr` and `Prover.toml`.
  The workspace also names `tests/core_deposit/circuit`, so its two files are read too; it
  is not built. ethsystems/pocs-private has the same commit.
- Witness inputs: the committed `Prover.toml` of each circuit at that commit.
- Noir libraries: poseidon v0.3.0 (git 0880c371), binary-merkle-root v0.0.2 (git ff307011).
  `check.sh` clones each tag once into `.deps/`, checks its commit and places it where nargo
  looks, so nargo fetches nothing.
- Later changes: after the pin, ethsystems/pocs-private pull request 16 (`748884e`, merged
  2026-10-08) changed `circuits/transfer/src/main.nr` and
  `contracts/src/verifiers/TransferVerifier.sol`. The package stays at `a04b8b3`; the newer
  transfer circuit is not covered here.

## Tools

- nargo 1.0.0-beta.21, noirc 1.0.0-beta.21+89a0f0faf3a5f1273c8ac4843b7877882437e277,
  binary sha256 0852cd5631ac5ca25f744f25c931e3cff16351d9bcdbfb03cebb48a4494a0fe3.
- noir-inspector 1.0.0-beta.21, binary sha256
  1928b997c6ec2f9d9461d60bc9481b47e599d6b338905d804aceb9510d832d84.
- Both binaries are in the release asset `noir-x86_64-unknown-linux-gnu.tar.gz` of
  https://github.com/noir-lang/noir/releases/tag/v1.0.0-beta.21 (asset sha256
  80c0343f9906d7fc0396c66da5891760b03ecfc9afc3c9bedd0fb4d38a58209e). `check.sh` checks the
  version and the sha256 of each binary; `TOOLS_UNPINNED=1` accepts another build of the
  same version.

## Pinned hashes

`expected.json` (`inputs`) pins, per circuit:

| Circuit | print (`noir-inspector print-acir`) | witness file (`nargo execute`) |
|---|---|---|
| deposit | a7b217947d30e7f5816efce1b9230790a907ddadfa76a339a647d457e69e9b4c | 78c512b9d207404cb8dfcfc5a90dba56994017a0414a0e12aeffb8e6cc62c55b |
| withdraw | 25510cf0c6cc6b8b8eb4168385d067cc31e2fbb1c47ae8f1386747009204aaf9 | 5167715eec99bee7249236687c6842de95bdc633488a08dbfa808aa67cbf192c |
| transfer | e2704cb56c12875712bcc428517eafe385298da51f5547e5422dd3ecac9564c9 | 2a877ff8f24250910272e8e66da6116e987db01d7919429f5e2498cb9485bf5b |

| Circuit | `func 0` section of the print | artifact `bytecode` (base64 string) | artifact `abi` |
|---|---|---|---|
| deposit | e09ceed51dbc595dfda5a274623261301663c553d344d89c3f0dae2f3693f78a | 86270f6e10ce9bbd051acb38624448cbf3fc3f689c8d28ff87c592f55ea14c58 | 2eca0103bb9f7ef1b1d235e4346b0f5d96698bab84a7b2f86e91e2f01ae323aa |
| withdraw | c68939b13f52dde72917c7e07880ff1c95cfbcbe2519d2f2c7340246b7ec1a3c | 19bf23cb31cf42560a69f9b0a2c20cceb16fbf0c86173375cea2c9e6412c3dc0 | 2c2b7d5898217e4289c0596b02d3aba8b35e41a37d76933bdfad07c48276b203 |
| transfer | dc747fb033334d70f691a3fbaef07ffd97b894b88714449aa9d42de759f91d5e | 8fcaf08feb8f5583f604a6987050bd56f5a505eb64961a6b4c96ea86bf22beb9 | adbc83d9dd1d4a998914a4a84141ea445a917b17d9dcf681d7086ed96eae6996 |

The `abi` hash is the sha256 of `json.dumps(abi, sort_keys=True, separators=(",", ":"))`.
The package does not pin a hash of the whole artifact: its `file_map` holds the absolute
path of each source file at build time, so the hash depends on where the build ran. The
other fields (`noir_version`, `hash`, `debug_symbols`) were equal in the archived and the
rebuilt artifacts.

## History

Until 2026-10-15 the package committed these nine outputs, compressed (4.2 MB), and
replayed them without a rebuild. They came from a build in the research repo
(oskarth/lean-shielded-pool at commit `fa5526e`), in two reviewed archives, one for
deposit and one for withdraw and transfer. A rebuild from the pocs submodule with the
pinned tools reproduced all nine: the print, `func 0`, bytecode, ABI, `noir_version` and
witness of each circuit are byte-identical to the archived ones; only the `file_map`
paths differ. Every generated Lean module kept its hash.

In the research repo, bb 5.0.0-nightly.20260324 (sha256
d7621dfb151f55c23fb04bf274f366a6a1e0516b85a3cf0ae9165a9952509793) regenerated
`DepositVerifier.sol`, `WithdrawVerifier.sol` and `TransferVerifier.sol` from these
artifacts, byte for byte equal to the committed files at a04b8b3. That ties the artifacts
to the committed verifier sources, not to deployed bytecode. This package does not re-run
that step.
