# shielded-pool-model

A small Lean 4 model of the shielded pool spec
([2/SHIELDED-POOL](https://github.com/ethsystems/specs/blob/4d4dce1/specs/2/README.md)),
with two machine-checked theorems about it, and ten separate packages
that check selected facts about the circuits, the contract, the
deployment and the client. Everything here re-runs with one command.
The core is meant to be read whole in an afternoon.

## The core claim

> The model covers the integrity rules of spec 2/SHIELDED-POOL,
> sections 4 to 6, at revision 4d4dce1 (exclusions in SPEC-MAP.md). In
> the model, the protocol rules imply two guarantees: no
> note spends twice, and value is conserved per token. Both hold from
> an empty pool, over every accepted history. One hypothesis is
> assumed, about the notes and keys that appear in that history. No
> two distinct notes with `u128` amounts share a commitment. No two
> distinct spending keys derive the same public key.
> Machine-checked with the three standard Lean axioms only. Whether
> the model says what the spec says is a human reading, not a
> machine check; one full reading (the second reader) and one
> high-level reading (Oskar) are done (REVIEW.md, part 5).

These are rows 2 and 3 of [CLAIMS.md](CLAIMS.md), which lists every
theorem with its hypothesis and spec clause. [SPEC-MAP.md](SPEC-MAP.md)
maps each definition to its spec line and lists the 16 simplifications
the model makes. The spec marks these two rows "machine-checked
(model)" on the strength of this repository.

## What is here

| Unit | Claim, in one line | Check |
|---|---|---|
| core model (`LeanShieldedPool/`) | the two theorems above, plus seven supporting results, epochs, the root window and a symbolic k-anonymity extension | `scripts/gate.sh`, about 2 minutes |
| [circuits-acir/](circuits-acir/README.md) | over the compiled constraints of the three circuits: amounts below 2^128, transfer conserves value | `check.sh`, about 17 minutes |
| [circuits-lampe/](circuits-lampe/README.md) | over the Noir source of the same circuits: the commitment, nullifier and Merkle-root equations hold for every accepting run | `scripts/check.sh`, about 25 minutes |
| [hash-agreement/](hash-agreement/README.md) | the Noir, plain and Solidity transcriptions of the Poseidon hash agree as functions | `check.sh`, about 1 minute |
| [verifier-reproduction/](verifier-reproduction/README.md) | the committed Solidity verifiers rebuild byte for byte from the circuits | `check.sh`, under 1 minute |
| [deployment/](deployment/README.md) | the Sepolia pool at block 11949456 equals a fresh build of pocs `a04b8b3`, byte for byte | `check.sh <rpc>`, about 4 minutes |
| [contract-halmos/](contract-halmos/README.md) | nine bounded symbolic suites on `ShieldedPool.sol`, 418 verdicts, 91 mutants that must fail | `check.sh`, about 80 minutes |
| [contract-kontrol/](contract-kontrol/README.md) | Kontrol proofs on the compiled contract: the guards before the verifier, the withdraw success path, the public inputs | `check.sh`, hours, in a pinned container |
| [refinement/](refinement/README.md) | under named premises, every accepted history of the contract refines a run of the model | `scripts/check.sh`, about 50 minutes |
| [client-verus/](client-verus/README.md) | 96 of 110 client functions have a selected property proved on a reviewed Verus mirror, 241 negative controls | `check.sh`, about 2 minutes |
| [privacy-games/](privacy-games/README.md) | conditional bounds on an attacker's advantage in two-world privacy games over the model | `scripts/check.sh`, about 8 minutes |

Each package is a directory with the same shape: a README (the claim,
what is not claimed, the trust base, the pins), one `check.sh`,
must-fail controls, and a `RESULT.md` from a fresh run. The packages
pin the code they check by commit or checksum; this repository is not a
copy of the implementation. The gate builds only the core.

Two documents collect the picture: [BOARD.md](BOARD.md), the 36-row
board of what the contract must do for the model to describe it, each
row citing a package; and [FINDINGS.md](FINDINGS.md), the 80 findings
of the campaign. Both are records, not claims.

## Scope

The claims stop where the checks stop. The theorems are about the
model. The packages check the circuits, the contract, the deployment
and the client at one pinned commit, each within the scope its README
states: bounded depths and byte lengths, mocked verifiers and tokens,
reviewed mirrors of the client code, privacy bounds that rest on hiding
or random-oracle premises. Nothing here runs the deployed system, and
nothing here is a soundness proof of the production verifier.
[SPEC-MAP.md](SPEC-MAP.md) says what a deployment must satisfy for the
model to describe it; each package README says what its PASS means and
what it leaves open.

## Re-check the core

You need git, bash, python3 and about 8 GB of free disk.

    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    git clone https://github.com/ethsystems/shielded-pool-model.git && cd shielded-pool-model
    lake exe cache get          # one-time setup; .lake is about 7.5 GB
    bash scripts/gate.sh        # expect: GATE PASS (<commit>)

The gate rebuilds from a fresh clone, rejects `sorry`, unlisted axioms
and `native_decide`, checks every statement in
[statements/INVENTORY.md](statements/INVENTORY.md) against its pinned
type, and runs the refutation controls. Each package README says how to
run its own check.

## Reading

Start with [CLAIMS.md](CLAIMS.md) and [SPEC-MAP.md](SPEC-MAP.md), then
the model (`LeanShieldedPool/Pool/`), the statements and the proofs.
[REVIEW.md](REVIEW.md) is the reviewer guide, with the format for
findings. [GUIDE.md](GUIDE.md) has the rest: where the model comes
from, the file layout, each package's claim in full, the map from the
writeup's sections to the repository, and the gate in detail.

## Status

The core proofs and gate are complete. The writeup
["Formally verifying a shielded pool: from spec to bytecode"](https://ethsystems.org/writeups/formally-verifying-a-shielded-pool-from-spec-to-bytecode/)
tells the story around this repository. Findings go in issues here, and
each gets an answer.

## License

File-level SPDX headers are authoritative. Code without a more
specific file-level license is licensed under MIT OR Apache-2.0
([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)).
Documentation, readmes and review notes are licensed under CC0-1.0
([LICENSE-CC0](LICENSE-CC0)) unless otherwise stated. Third-party
dependencies, including the pinned sources that the separate packages
fetch, keep their own licenses.
