# Where the inputs come from

`check.sh` replays the proofs from these files. It does not recompile the Noir
circuits. The compile, print and solve steps below ran in the research repo
(oskarth/lean-shielded-pool); their records are cited, not re-run.

## Files

| File | What it is | sha256 of the decompressed content |
|---|---|---|
| `deposit.acir.txt.xz` | `noir-inspector print-acir target/deposit.json` | a7b217947d30e7f5816efce1b9230790a907ddadfa76a339a647d457e69e9b4c |
| `withdraw.acir.txt.xz` | same, withdraw | 25510cf0c6cc6b8b8eb4168385d067cc31e2fbb1c47ae8f1386747009204aaf9 |
| `transfer.acir.txt.xz` | same, transfer | e2704cb56c12875712bcc428517eafe385298da51f5547e5422dd3ecac9564c9 |
| `deposit.json.xz` | nargo artifact (ABI, bytecode, debug data, embedded sources) | c14f69a0123f6095a7f645bfe20f0f999eb8b455bfd809d9e6bb90719c44da38 |
| `withdraw.json.xz` | same, withdraw | e798d4c6f7028b9172de2dd472f693d9ed539bfedaa0b465e3c616a077d6448e |
| `transfer.json.xz` | same, transfer | 4d337288ee4c8ec800e66372b72036623353d9eb9cc3725bfb901bec605d5098 |
| `deposit-witness.gz` | `nargo execute` witness for the committed Prover.toml (file itself) | 78c512b9d207404cb8dfcfc5a90dba56994017a0414a0e12aeffb8e6cc62c55b |
| `withdraw-witness.gz` | same, withdraw | 5167715eec99bee7249236687c6842de95bdc633488a08dbfa808aa67cbf192c |
| `transfer-witness.gz` | same, transfer | 2a877ff8f24250910272e8e66da6116e987db01d7919429f5e2498cb9485bf5b |

`expected.json` pins these values, the hash of each compressed file, the hash of
each `func 0` section and of each artifact's bytecode string:

| Circuit | `func 0` section | bytecode (base64 string) |
|---|---|---|
| deposit | e09ceed51dbc595dfda5a274623261301663c553d344d89c3f0dae2f3693f78a | 86270f6e10ce9bbd051acb38624448cbf3fc3f689c8d28ff87c592f55ea14c58 |
| withdraw | c68939b13f52dde72917c7e07880ff1c95cfbcbe2519d2f2c7340246b7ec1a3c | 19bf23cb31cf42560a69f9b0a2c20cceb16fbf0c86173375cea2c9e6412c3dc0 |
| transfer | dc747fb033334d70f691a3fbaef07ffd97b894b88714449aa9d42de759f91d5e | 8fcaf08feb8f5583f604a6987050bd56f5a505eb64961a6b4c96ea86bf22beb9 |

The pinned artifacts retain original build paths, including a worker
identifier, in compiler metadata. Replay does not use those paths. They
remain to preserve the archived artifact hashes.

## Sources and tools

- Circuits: ethsystems/pocs-private `a04b8b38969dfc2ee64de47edee7e396454204a8`,
  `pocs/private-payment/shielded-pool/circuits/{deposit,withdraw,transfer}`, exported
  with `git show`. `src/main.nr` sha256: deposit 7d1b3c3347415023fe2e7e193663f28beaf3a042d0628b04d64bbcc8aa515391,
  withdraw a987c5ba151a9dafa03ff3cc3082a210f2ab098a89d0f89b4a87b5addf84b974,
  transfer 33ab018365efdc2107ae31bba10978ee878bf316c6bf4d51de777c0c9b1b8cfd.
  `Nargo.toml` sha256: deposit 943dd0ccf79c52d54fe7b82c8eb9c714ab4b186c4e225fc8316f5c17bc1ec4c3,
  withdraw bf3f9ce44081660bad67a0ad775af00e0603b9066dc5d8739ba03523f82d60d1,
  transfer e5fd8e9f7835106096fb5da834ebc00ec95ab3c71e8b17963403fa81ba34fc18.
- Witness inputs: the committed `Prover.toml` of each circuit at the same revision
  (sha256 deposit d35f0c1de32062769a1e2711a580e153975a8d1d3109c3c53afd015f20199322,
  withdraw 1ad20cfd7cd091b38dbaa9fe7e161913bb80a40a3f5f2051d56af87403e69fc2,
  transfer 96620f05ad8f524fa43b123c942e3bb343c8c708f5dcde14160f342425f6e922).
  These files are not included.
- Noir dependencies: poseidon v0.3.0 (git 0880c371), binary-merkle-root v0.0.2
  (git ff307011).
- Tools: nargo 1.0.0-beta.21, noirc 1.0.0-beta.21+89a0f0faf3a5f1273c8ac4843b7877882437e277
  (binary sha256 0852cd5631ac5ca25f744f25c931e3cff16351d9bcdbfb03cebb48a4494a0fe3),
  noir-inspector beta.21 (sha256 1928b997c6ec2f9d9461d60bc9481b47e599d6b338905d804aceb9510d832d84),
  bb 5.0.0-nightly.20260324 (sha256 d7621dfb151f55c23fb04bf274f366a6a1e0516b85a3cf0ae9165a9952509793).

## Earlier reproduction (research repo, not re-run here)

- A recompile of withdraw and transfer from the archived a04b8b3 sources reproduced the
  `func 0`, bytecode and witness hashes above ("PROVENANCE MATCH").
- A fresh rerun of the deposit pipeline from the same sources reproduced its hashes
  ("RERUN MATCH").
- bb 5.0.0-nightly.20260324 regenerated `DepositVerifier.sol`, `WithdrawVerifier.sol` and
  `TransferVerifier.sol` from these artifacts byte for byte equal to the committed files at
  a04b8b3. That ties the artifacts to the committed verifier sources, not to deployed
  bytecode (a judged archive record).

Records: two archives in the research repo (oskarth/lean-shielded-pool at
commit `fa5526e`), one for deposit and one for withdraw and transfer, each
with a cross-family judgment.
