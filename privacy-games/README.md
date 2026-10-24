# privacy-games: two-world privacy games over the shielded-pool model

This package states privacy as games over the model of the parent directory and proves
conditional bounds on the attacker's advantage in them. It replaces the frozen report
[evidence/2026-10-06-privacy-games/privacy.md](../evidence/2026-10-06-privacy-games/privacy.md):
the games, bounds, counterexamples and funded examples of that report are the Lean theorems
here, and `scripts/check.sh` rebuilds them and checks their axioms. The package is separate
from the gated model: it has its own lakefile, uses the same toolchain (Lean 4.33.1, Mathlib
`0df444a`) and adds VCV-io (`dfc7ff07`) for oracle computations and probability. It imports
three model files of the parent unchanged (below) and changes nothing in them. Nothing here
changes the claim in the parent README.

None of this is a privacy claim about the deployed pool. Every bound carries premises that
no real hash is shown to meet, and attackers who act after they see challenger events are
not covered.

## The model files

The games import `LeanShieldedPool/Pool/State.lean`, `Tx.lean` and `Events.lean` of the gated
model, and lake compiles them from the parent directory (`lean_lib Model`, `srcDir = ".."`).
The package has no copy of the model. [PINS.sha256](PINS.sha256) pins the SHA-256 of the
three files, and the check fails when one of them changes. The games are checked against the
current transfer guard: input 0 must be a member of the tree; input 1 can be ballast.

## What the games model

An experiment has two worlds that differ only in the secret under test, for example which of
two recipients a transfer paid. A challenger flips a hidden coin, runs one world through the
model's guards, and shows the attacker that game's public record. The attacker guesses the
coin. The advantage is the absolute bias of the attacker's success probability from 1/2.

The observed record is narrow, and each game fixes its own permitted public differences.
There is no theorem for the complete transaction view. The recipient games expose the ordered
commitment and nullifier event log. The honest-key games also give the attacker the public
keys. Proofs, Merkle roots, encrypted payloads, timing and network data are outside every
game. An illegal or rejected challenge returns a fair win bit and does not call the
observer. Every published history is an accepted execution of the model, with that game's
primitives. A modeled execution is not a refinement result about an implementation.

In the random-oracle games, the hash uses that the game names are independent uniform
functions, and the attacker can query them a bounded number of times. This premise (A8 in
the frozen report) is a heuristic. It is stronger than collision resistance. The Merkle-node
use of Poseidon2 is outside these games.

## Notation

L counts setup and history operations; m bounds the minted leaves after setup; n bounds the
challenge transfers. S, C and K are the sizes of the sampled salt, commitment and key sets.
q = qc + qg counts the worst-case queries across the modeled oracles. qC and qN are positive
spread parameters: each relevant point probability is at most 1/qC or 1/qN; they are not
query counts. N counts honest accounts. U = |Token| * cap * |PubKey| * S is the full
commitment-oracle domain, and B3 = U(U-1)/(2C). H = 2n(qc+qg+4L+6n)/S;
H0 = 2n(qc+4L+6n)/S; D = 2n(2L+2n)/C; E3 = (2mn+n(2n-1)+2tn)/S. k in the chain bound, or t in
E3, bounds the protected nullifier targets of each output. R is the rejection probability
(the illegality term). V is the validity-failure probability of the static commit-only game;
V3 is the probability of an injective table that fails `TableValid`.

## The bounds

All names below start with `LeanShieldedPool.`.

| Game | What is hidden | Theorem | Bound (plain form) | Premises | Status |
|---|---|---|---|---|---|
| Static transfers | the recipient of n transfers | `RecipientGame.Rejection.advantage_le` (general form `RecipientGame.advantage_le`: 2n*epsHiding + R/2) | 2n*epsHiding + delta/2, delta = (2mn + n(2n-1))/qC | commitment hiding with error epsHiding (`BoundAssumptions`) and commitment spread (`CommitmentSpread qC`); an accepted common setup; well-formed worlds whose deterministic guards hold after every earlier salt assignment, also in unchecked states after collisions (`WellFormedAdversary`) | proved; no useful Poseidon instantiation of the hiding premise is shown |
| Fixed chains | the recipient along spend chains fixed in advance | `ChainGame.advantage_le_delta` | 2n*epsHiding + (delta + 2kn/qN)/2 | the hiding premise plus nullifier spread (`NullifierSpread qN`); chains fixed in advance with equal backward references, snapshots and spending keys; recursive validity certificates protect the later nullifier checks | proved; the same hiding limit |
| Withdrawal, random oracle | which note a withdrawal spends | `WithdrawGame.ROM.advantage_le_queryBound` | N(qc+qg)/K + N(N-1)/K + R/2 | the random-oracle premise for two oracles (key derivation, nullifier); every account honest, with keys that the challenger samples; the attacker holds no account, spending or viewing key, or payload, so counterparty attackers (a recipient who decrypts a salt, a depositor who built the note) are excluded | proved; R has no numeric bound |
| Owner and sender, random oracle | the deposit owner; the transfer sender | `OwnerGame.ROMCommit.advantage_le_queryBound`, `SenderGame.ROMCommit.advantage_le_queryBound` | owner: (q+4L)/S + R/2; sender: Nq/K + N(N-1)/K + (2(q+6L+4)+1)/S + R/2 | the random-oracle premise for three oracles (with the commitment); the same honest-account restriction; history length at most L; challenge amounts below cap = 2^128; no hiding premise | proved; R has no numeric bound |
| Static transfers, commit-only | the recipient of n transfers | `RecipientGame.CommitOnly.advantage_le_queryBound`, `RecipientGame.CommitOnly.advantage_le_rom_collisions`, `RecipientGame.CommitOnly.advantage_le_birthday` | H + R/2; R <= H0 + D + V | the random-oracle premise for the commitment only; `derivePub` and `nullify` fixed; uniform sampling | proved; V has a birthday bound under `ValidOn`; a useful bound with an explicit nullifier-collision charge is open |
| Chains, commit-only | the recipient along a funded chain | `ChainGame.CommitOnly.advantage_le_queryBound`, `ChainGame.CommitOnly.advantage_le_rom_collisions` | H + R/2; R <= V3 + B3 + E3 | as above, plus `commit` injective in the salt at or above the cap, and `nullify` injective for each key | proved; vacuous unless C > U(U-1)/2, so not for production parameters |

The seventh row of the frozen report, symbolic k-anonymity, is the gated extension
`LeanShieldedPool/Extensions/KAnonymity.lean` of the parent, not part of this package.

Three reading rules:

1. The premises of a row are part of its claim. A bound quoted without them says nothing.
2. A bound with an R or V3 term is only as strong as that term.
3. The V bound of the static commit-only game: for a fixed list xs of h distinct hashed
   coordinates, `ValidOn` gives V <= h(h-1)/(2C). `ValidOn` requires an accepted setup and
   valid worlds at every table injective on xs, for every supported choice. For two hashed
   inputs spent under one key, that forces `nullify` to be injective in the commitment for
   that key. A choice that depends on the oracle needs xs to cover every coordinate it can
   spend. The general H + R/2 bound keeps V and needs no injectivity premise.

The same games also have standard-model forms with a PRF or hiding premise instead of a
random oracle: `WithdrawGame.Transport.advantage_le` (epsPRF + R/2),
`OwnerGame.advantage_le` (epsHiding/2 + R/2) and `SenderGame.advantage_le`
(eta + epsHiding + R/2); `SenderGame.ROM.advantage_le_queryBound` is the sender game with two
oracles and a hiding premise. The commitment random oracle that the three-oracle games share
is in `CommitROM/`.

## The two counterexamples

Both are proved negations on the standard axioms, not failures to find a proof.

1. When the attacker writes both worlds, a watcher links a withdrawal to its note.
   `ChosenWorldGame.Counterexample.concrete_counterexample`: in a built example (salts of
   size 32) the hiding error is 0, the rejection probability is at most 3/16, and the
   advantage is at least 13/32. `ChosenWorldGame.Counterexample.transported_bound_false`:
   the advantage is not at most 3*epsHiding + (6/32)/2 = 3/32, the bound that the static
   recipient premises would allow. The example does not need the key, because its toy
   nullifier equals the commitment; the linkage through knowledge of the key is the separate
   lemma `ChosenWorldGame.known_key_links`. The attacker model that is right for recipient
   privacy is wrong for withdrawal privacy.
2. In the honest-key withdrawal toy, the attacker wins with probability 3/4, so the advantage
   is 1/4 (`WithdrawGame.Toy.toy_advantage`), while the PRF and hiding errors are 0 and every
   history is accepted (`WithdrawGame.Toy.toy_obstruction`). Its public key equals one
   nullifier value (`WithdrawGame.Toy.toy_public_key_prf_distance`). The toy meets a
   public-key-blind, information-theoretic premise on the full table at error zero, so it
   refutes the zero-error bound (`WithdrawGame.Toy.toy_zero_error_bound_false`,
   `WithdrawGame.TransportControls.toy_drop_premise`). It does not refute bounds with a
   spread allowance of at least 1/4, and it is not an attack on spec 2. The premises must
   name every value that the observer sees.

These two results show why the earlier premises were not sufficient. They do not show that
a particular repair is sufficient. The other `toy_*` theorems of `WithdrawGame/`,
`OwnerGame/Toy.lean` and `SenderGame/` are smaller controls of the same kind: each drops one
premise and shows that the bound then fails.

## The funded examples

- The salt-collision fixture deposits one unit and spends it at snapshot 1. Its rejection
  probability is exactly 5/8 (`RecipientGame.Rejection.Fixture.rejection_eq_five_eighths`),
  so the 1/4 bound is false for it (`FundedWorlds.funded_quarter_bound_false`), and its
  advantage is at most 2*epsHiding + 5/16 (`RecipientGame.Rejection.Fixture.advantage_le`).
- On the current transfer guard, no nonempty transfer-only world is realizable
  (`FundedWorlds.nonempty_world_not_realizable`; `FundedWorlds.empty_transfer_guard_false`).
  So the transfer-only correspondence obligations of `GameCorrespondence` hold only for empty
  worlds. A funded realization, with a deposit before the transfers, is the only shape that
  works (`FundedWorlds.funded_world_has_realization`). To change the obligation structures to
  that funded form is open work.
- Static commit-only, one deposit spent by one transfer (L = n = 1), with S = C = k + 8:
  validity failure exactly 0 (`RecipientGame.CommitOnly.Funded.validity_zero`), rejection at
  most 32/(k+8) (`Funded.rejection_bound`), funded acceptance at least 1 - 33/(k+8)
  (`Funded.funded_pass_lower_bound`), advantage at most 40/(k+8) (`Funded.privacy_bound`).
- The pair witness, two deposits spent by one transfer: V = 1/C exactly
  (`RecipientGame.CommitOnly.TwoFunded.validity_exact`), advantage at most 101/(2C)
  (`TwoFunded.privacy_bound`).
- The funded chain has two transfers; the second spends the outputs of the first. Its
  advantage is at most 75/(k+8) + 6(k+8)(6(k+8)-1)/(4(k+8)^4)
  (`ChainGame.CommitOnly.FundedChain.privacy_bound`); the chain takes C = S^4 to make B3
  small.
- At k = 65528 (S = 65536) the advantages are below 1/1000, and below 1/800 for the chain
  (`Funded.small_terms`, `TwoFunded.small_bounds`, `FundedChain.small_bounds`).

What they show: the games accept value-moving histories, and the bounds evaluate to small
numbers there, so the theorems are not vacuous in these models. What they do not show:
privacy in production. The guesses of the witnesses are constant or close to it (qg = 0 or
1), so they do not stress the hiding terms. V = 0 holds for the first witness only because
its choice falls back to empty worlds on a collision. The chain parameters are chosen to be
favorable. The toy primitives (`nullify` as the identity) meet the injectivity premises
trivially.

## What is not claimed

- No privacy claim about the deployed pool, the contracts, the circuits or the client.
- No Poseidon instantiation: no theorem connects a hiding, spread or random-oracle number to
  the deployed Poseidon parameters. Under a random-function heuristic, Poseidon4 with a salt
  uniform over the full field has a hiding distance of about 0.52 (epsHiding about 0.26), so
  a bound that starts 2n*epsHiding is above 1/2 for n >= 1. This is a hand estimate, not a
  Lean result; it is why the commit-only random-oracle games exist.
- The random-oracle premise (A8) is a heuristic.
- Interactive attackers are open: choices made after challenger events, adaptive
  corruption, and later disclosure of a key or a salt. The random-oracle games let the
  attacker query the oracles before it fixes the whole challenge; that is not an interactive
  transaction schedule.
- Open: a bound on V with an explicit nullifier-collision charge and no nullifier
  injectivity; a chain rejection bound that is not vacuous at production parameters (B3
  ranges over the whole commitment-oracle domain); a numeric bound on the R terms of the
  random-oracle games; later spends beyond fixed chains; observations of visible reverts.

## Trust base

- The Lean kernel, and the three axioms `propext`, `Classical.choice` and `Quot.sound`.
- Mathlib at `0df444a` and VCV-io at `dfc7ff07`, with their dependencies (PolyFun, loom2,
  cslib, Batteries, Aesop and the others in `lake-manifest.json`), as pinned. The check
  builds the VCV-io modules that the games import from source and uses Mathlib's prebuilt
  oleans (`lake exe cache get`).
- The three model files of the parent, at their pinned hashes.
- Not trusted: the game modules, the census, the controls and the scripts. The census and the
  scans are checks against mistakes, not against a hostile package: code that runs during
  elaboration could change what the census prints.

## Pins

[PINS.sha256](PINS.sha256) holds the pins as `# key value` lines and sha256sum lines:

- VCV-io: `https://github.com/dtumad/VCV-io` at `dfc7ff078f3dbca0e71c40e289b9db175ab7ce16`.
- Mathlib: `https://github.com/leanprover-community/mathlib4` at
  `0df444a360eaa60ab8c11dca51a86af692955474` (the tag `v4.33.1`, the Mathlib of the gated
  model and of VCV-io's own manifest).
- Lean `v4.33.1` (`lean-toolchain`).
- The SHA-256 of `../LeanShieldedPool/Pool/State.lean`, `Tx.lean` and `Events.lean`.

`lakefile.toml` requires VCV-io and Mathlib by git at these commits; `lake-manifest.json`
records the resolved dependencies.

## Re-check

Install git, bash, python3 (3.10 or later), sha256sum and elan. Clone the whole repository:
the package compiles three files of the parent directory. The first run downloads VCV-io,
Mathlib and Mathlib's prebuilt oleans (about 8.3 GB in `.lake`).

```
cd privacy-games
scripts/check.sh      # expect the last line: CHECK PASS: ...
```

Set `JOBS` to compile several controls at once and `LEAN_NUM_THREADS` (default 2) for lake.
[RESULT.md](RESULT.md) records a run, with times and peak memory.

`scripts/check.sh` runs, in order:

1. the tools: Lean 4.33.1 through lake, python3, git;
2. the pins (`scripts/pins.py`): `lean-toolchain`; VCV-io and Mathlib in `lakefile.toml`
   and `lake-manifest.json`; the SHA-256 of the three model files;
3. a source scan of every Lean file of the package for `sorry`, `admit`, `native_decide`,
   `axiom`, `opaque`, `extern`, `implemented_by`, `unsafe` and `skipKernelTC`, and of
   `lakefile.toml` for kernel options;
4. the rename check (`scripts/check-rename.py`, below);
5. the fetch: `lake exe cache get`, then the pins again, now also on the fetched checkouts:
   VCV-io and Mathlib at their commits, VCV-io's own manifest on the same Mathlib, and no
   change or untracked file in the VCV-io tree;
6. the build: `lake build`, with no warning allowed in a package module;
7. the census (`Census.lean`, `scripts/census.py`): every theorem of the package and of the
   three model modules, auxiliary ones included, depends on a subset of the three axioms; no
   module declares an axiom or an opaque constant; the census imports every module; the
   non-auxiliary theorems, their printed statements and the SHA-256 of their raw types equal
   [statements/INVENTORY.md](statements/INVENTORY.md) and `statements/RAW.sha256`; it
   prints the counts of modules, declarations and theorems;
8. the controls (`scripts/controls.py`): `scripts/gen-controls.py` must reproduce the Lean
   controls of `controls/`; each planted failure must fail with the first error in
   `controls/EXPECTED.tsv`; each unchanged copy must compile.

## The census counts

The census counts the declarations written in the source (a `def`, `abbrev`, `theorem`,
`lemma`, `structure`, `inductive` or `instance`; not the constructors, projections and other
names that Lean generates) and the theorems among them. The run in RESULT.md gives 82
modules, 1,450 declarations and 775 theorems, and 48 declarations in the three model files.
The frozen report counted 1,487 declarations and 769 theorems with a different method: a
list of the named declarations of the same sources, with the 48 of the model files, without
the five anonymous instances of `SenderGame/`, and without the six `FundedWorlds` theorems,
which were outside that list. 1,487 - 48 + 5 + 6 = 1,450, and 769 + 6 = 775. The census also
counts 2,079 theorems with the auxiliary ones; 959 of them are listed in the inventory.

## The controls

[controls/EXPECTED.tsv](controls/EXPECTED.tsv) lists 20 planted failures and 8 copies that
must compile. Eighteen adapt the planted cases of the earlier replay of these games, which
altered one source byte of eight modules, removed eight headline theorems from the audit
lists, and changed the VCV-io tree twice:

- eight Lean controls: a game module cut after its headline theorem, with one change to the
  theorem's statement (a term halved, quartered or dropped) and none to its proof; each must
  fail at that theorem, not by a parse error or an unknown name. Their `same_` copies, the
  same cuts unchanged, must compile;
- eight census controls: a copy of `statements/` with one headline theorem removed, its
  statement changed, or its raw hash changed or removed; the census must fail;
- two pin controls: a tracked change and an untracked file in the VCV-io checkout, each
  undone at once; the pins must fail.

Two more pin controls are new: a manifest that resolves VCV-io to another commit, and a copy
of the model files with one byte added. A failing control shows that the checks reject that
change. It does not show that the changed statement is false.

## Layout

- `PoolGame/`: the game interface (`Basic`: the observer view as a VCVio oracle interface,
  the transfer indistinguishability game, the primitive assumptions), and the averaging
  lemmas (`Summand`, `Averaging`).
- `GameCorrespondence.lean`: the map from the model's primitives and events to the game
  interface, the observer correspondence, and the obstruction to realizing every legal world.
- `RecipientGame/`: the recipient of static transfers: the game and the general bound
  (`Basic`), the rejection bounds and the fixtures (`Rejection`), the funded worlds
  (`FundedWorlds`), the random-oracle form (`ROMCommit/`) and the commit-only form
  (`CommitOnly/`).
- `ChainGame/`: the recipient along fixed chains (`Basic`, `AdaptiveRejection`,
  `AdaptiveExample`) and its commit-only form (`CommitOnly/`).
- `ChosenWorldGame/`: withdrawal when the attacker writes both worlds, with the first
  counterexample.
- `WithdrawGame/`: withdrawal with honest keys: the game, the PRF transport, the toys and the
  second counterexample, and the random-oracle form (`ROM/`).
- `OwnerGame/`, `SenderGame/`: the deposit owner and the transfer sender, with their toys and
  random-oracle forms.
- `PrivacyTools/`: probability lemmas shared by the owner and sender games.
- `CommitROM/`: the commitment random oracle that the three-oracle games share.
- `Census.lean`; `statements/`: the inventory and the raw-type hashes.
- `controls/`: the Lean controls and `EXPECTED.tsv`.
- `scripts/`: `check.sh`, `pins.py`, `census.py`, `controls.py`, `gen-controls.py`,
  `rename.py`, `check-rename.py`, `rename-map.txt`, `rename-origins.txt`.
- `PINS.sha256`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `RESULT.md`.

## Earlier names

The modules were first written with working names: a game number per experiment (Game2 to
Game7) in one flat module directory. `scripts/rename-map.txt` maps each earlier module and
namespace, and one theorem name, to its name here, so that older reports can be read against
these files: Game2 is `RecipientGame`, Game3 `ChainGame`, Game4 `ChosenWorldGame`, Game5
`WithdrawGame`, Game6 `OwnerGame` and Game7 `SenderGame`. `scripts/check-rename.py` applies
the map backwards to every module, removes the comments, and compares the SHA-256 of the
result with the original's in `scripts/rename-origins.txt`: the modules differ from their
first form only in names and comments. The audit modules of the first form (lists of
`#print axioms`) are not here; the census replaces them.
