> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-06.
> Sanitised for publication: see [../README.md](../README.md).

# Claim 2: privacy, prospective

These privacy results are ported (PRIVPORT) to the repinned model. The pre-repin results remain replayable at `753c60b`.

Chapter for the research-phase writeup, section 6 (written by Fable; v2 after a cross-family
review, all nine items applied; zero new proofs; sources: LEDGER rows 8-9 (ported, PRIVPORT), A6,
A8, and the research-phase judge records; chapters 8-42 of the research chapter log, historical,
LEDGER wins).

**Lead.** Safety says what can happen; privacy says what an observer can compute, so it lives in
games, not in the safety model. Lean proves conditional privacy bounds for specified event-log
experiments, and selected funded examples show some bounds are non-vacuous in those models. None of
this proves privacy of the deployed system: every bound carries premises a real hash has not been
shown to meet, and interactive attackers, who act after seeing challenger events, remain open (the
existing games already allow oracle queries before the challenge is fixed). This chapter states each
result with its limit, and what the failures taught us.

## What the games model

An experiment has two worlds that differ only in the secret under test, for example which of two
recipients a transfer paid. A challenger flips a hidden coin, runs one world through the frozen
model's guards, and shows the attacker that game's public record. The attacker guesses the coin.
Advantage means the absolute bias of the attacker's success probability from 1/2.

The observed record is deliberately narrow, and each game fixes its own permitted public differences;
there is no theorem for the complete transaction view. Recipient games expose the ordered
commitment/nullifier event log. Honest-key games also give the attacker the public keys. Proofs,
Merkle roots, encrypted payloads, timing, and network data remain excluded everywhere. Illegal or
rejected challenges return a fair win bit without invoking the observer. Every published history is
an accepted execution in the frozen model, using that game's primitives (the chapter-30 negation
forced this repair); a modeled execution is not an implementation-refinement result. In the
random-oracle experiments, A8 idealizes the stated hash uses as independent uniform functions the
attacker may query a bounded number of times; it is a heuristic, stronger than collision resistance,
and the Merkle-node use of Poseidon2 is outside these games.

## Notation

L counts setup/history operations; m bounds minted leaves after setup; n bounds challenge transfers.
S, C and K are the sampled salt, commitment and key-set sizes. q = qc + qg counts worst-case queries
across the modeled oracles. qC and qN are positive spread parameters: each relevant point probability
is at most 1/qC or 1/qN; they are not query counts. N counts honest accounts. U = |Token| * cap *
|PubKey| * S is the full commitment-oracle domain, and B3 = U(U-1)/(2C). H = 2n(qc+qg+4L+6n)/S;
H0 = 2n(qc+4L+6n)/S; D = 2n(2L+2n)/C; E3 = (2mn+n(2n-1)+2tn)/S. k in the older Game3 bound, or t in
E3, bounds each output's protected nullifier targets. R is rejection probability. V is Game2
validity-failure probability; V3 is the probability of an injective table that fails TableValid.

## The proved bounds

| Game | What is hidden | Bound (plain form) | Premises | Status |
|---|---|---|---|---|
| Game2, static transfers | recipient of n transfers | 2n*epsHiding + delta/2, delta = (2mn + n(2n-1))/qC | A6 hiding and commitment spread; accepted common setup; well-formed worlds whose deterministic guards hold after every prior salt assignment, including unchecked states after collisions | Proved; no useful Poseidon instantiation of the hiding premise is demonstrated |
| Game3, fixed chains | recipient along pre-fixed spend chains | 2n*epsHiding + (delta + 2kn/qN)/2 | A6 plus nullifier spread; chains fixed in advance with equal backward references, snapshots and spending keys; recursive validity certificates protect later nullifier checks | Proved; same hiding limit |
| Stage 5 ROM, withdrawal | which note a withdrawal spends | Nq/K + N(N-1)/K + illegality/2 | A8 (two oracles); every account honest with challenger-sampled keys; the attacker holds no account, spending/viewing key, or payload, which excludes counterparty attackers (a recipient who decrypts a salt, a depositor who built the note) | Proved; illegality has no numeric bound |
| Stage 6 ROM, owner and sender | deposit owner; transfer sender | owner: (q+4L)/S + illegality/2; sender: Nq/K + N(N-1)/K + (2(q+6L+4)+1)/S + illegality/2 | A8 (three oracles); the same honest-account restriction; history length bounded by L; challenge amounts below cap = 2^128; no hiding premise | Proved; illegality unbounded |
| Stage 7b, commit-only Game2 | recipient, static transfers | H + R/2; R <= H0 + D + V | A8 for the commitment only; derivePub and nullify fixed; uniform sampling | Proved; V has a birthday bound under ValidOn; a useful bound with an explicit nullifier-collision charge remains open |
| Stage 7b, commit-only Game3 | recipient along a funded chain | H + R/2; R <= V3 + B3 + E3 | As above, plus commit salt-injective at or above the cap and nullify injective per key | Proved; vacuous unless C > U(U-1)/2, so not for production parameters |
| Symbolic k-anonymity | recipient, counting explanations | an anonymity set of size two, machine-checked | opaque-label observer (a named hiding abstraction); toy primitives that ignore ownership | Proved in its restricted model |

Three reading rules. First, each row's premises are the claim; quoting a bound without them says
nothing. Second, the bounds with an illegality or V3 term are only as strong as that term. Third,
the Game2 V bound: for a fixed distinct list xs of h hashed coordinates, ValidOn gives
V <= h(h-1)/(2C). ValidOn requires accepted setup and valid worlds at every table injective on xs,
for every supported choose result. For two hashed inputs spent under one key, that condition forces
nullify to be injective in the commitment for that key. An oracle-dependent choose needs xs to cover
every coordinate it may spend. The general H + R/2 bound retains V and needs no such injectivity
premise.

## The two toy counterexamples, and what they taught

Both are proved negations on the standard axioms, not failures to find a proof.

The first (chapter 38): when the attacker writes both worlds, a watcher links a withdrawal to its
note, with advantage at least 13/32 in a fully built example while the premises allow 3/32. The
corrected reading matters: the concrete counterexample does not even need the key, because its toy
nullifier equals the commitment; the key-knowledge linkage is a separate general lemma. Lesson: the
attacker model that is right for recipient privacy is wrong for withdrawal privacy.

The second (chapter 40): in the honest-key toy, the attacker wins with probability 3/4, giving
advantage 1/4; its public key equals one nullifier value. The toy satisfies a public-key-blind,
information-theoretic full-table premise at error zero, so it refutes the stated zero-error bound.
It does not refute bounds with an additional spread allowance of at least 1/4, and it does not
demonstrate an attack on spec 2. Lesson: premises must name every value the observer sees.

These two results show why the earlier assumptions were insufficient and guide the revised games.
They do not establish that any particular repair is sufficient.

## The funded examples: what they show and do not show

The ported (PRIVPORT) SaltCollision fixture has a deposit prefix and snapshot 1. Its rejection probability is exactly 5/8.
A control refutes the funded 1/4 bound. Its advantage bound is 2*epsHiding + 5/16.
WellFormed-conditioned bounds now require input-0 membership. General games, interfaces, and formulas are unchanged.

On the repinned model, nonempty transfer-only worlds are unrealizable outright (PortControls), so the transfer-only correspondence obligations are satisfiable only for empty worlds; the funded realization is the only viable correspondence shape, and revising the obligation structures to funded form is follow-up work, not part of this port.

The stage 7b witness is one deposit spent by one transfer (L = n = 1): validity failure exactly 0,
rejection at most 32/(k+8), funded acceptance at least 1 - 33/(k+8), advantage bound 40/(k+8). The
pair witness (two deposits spent by one transfer) evaluates V = 1/C exactly and gives
advantage at most 101/(2C); its funded Game3 chain has two transfers, the second spending the
first's outputs, and gives advantage below 1/800. The small-bound evaluations use k = 65528, so
S = 65536; the Game2 examples have C = S, and the Game3 witness takes C = S^4 to make B3 small.

What they show: the experiments accept value-moving histories within their models, and the bounds
evaluate to small numbers there, so the theorems are not vacuous in those models. What they do not
show: production privacy. The witness guesses are constant or near-constant (qg = 0 or 1), so they
do not stress the hiding terms; V = 0 holds for the first witness only because its choose retreats
to empty worlds on a collision; the Game3 parameters are chosen to be favorable; and the toy
primitives (nullify as identity) meet the injectivity premises trivially.

## What is open

- Bound V by the commitment-table collision probability plus an explicit nullifier-collision charge,
  without assuming nullifier injectivity.
- A Game3 rejection bound that is non-vacuous at production parameters (B3 ranges over the whole
  commitment-oracle domain U; a query-local version is the open shape).
- A numeric bound on the illegality terms in the stage 5 and 6 games.
- Interactive choices made after challenger events, adaptive corruption, and later key or salt
  disclosure. The existing ROM choose phase can query its oracles before selecting the complete
  challenge; that is not an interactive transaction schedule.
- Later spends beyond fixed chains, and observations of visible reverts.
- Connecting any spread or hiding number to deployed Poseidon parameters (A8 stays a heuristic).

## The lesson for method

The hiding-based route failed for a quantitative reason worth recording. Poseidon4 with a salt
uniform over the full field is not known to meet information-theoretic hiding at small error: under
a random-function heuristic, its hiding distance is about 0.52, epsHiding about 0.26, so a bound
that starts 2n*epsHiding exceeds 1/2 for n >= 1. For the reference client's 216-bit salt, the same
heuristic predicts distance near 1. These are hand estimates, not Lean results and not proved
Poseidon lower bounds; A8 remains a heuristic with unpinned Poseidon parameters. That is why the
commit-only random-oracle route exists, where the hiding term is replaced by counted oracle queries.

The wider lesson is the project's recurring one: the machine kept finding the gaps in the words.
The first game leaked through its log length until illegal pairs got a provable fair coin; stage 7
was true and said nothing because it drew the key oracle after the fixed setup; the game-to-model
correspondence was a proved negation until the referee ran the model's own guards; and each judge
pass since has made a claim say less and mean more. A privacy bound for this pool will be built the
same way, one named premise at a time, or it should not be quoted at all.

Replay: `scripts/recheck.sh privacy <new-out-dir>` checks the ported sources against the current model pins.
The reviewed PRIVPORT replay rebuilt 96 modules and audited 1,487 declarations, including 769 theorems, with standard axioms only.
It includes stages 1-7b and the pair witness. It trusts prebuilt VCV-io dfc7ff07, Mathlib, and the Lean v4.33.1 binary.
The main gate excludes these evidence privacy sources.
The historical replay at `753c60b` audited 1,478 declarations; its validation driver rejected 18 planted cases.
That driver remains historical. The current replay is dated 2026-10-06.

(No disagreements: all nine review items applied; two status changes were re-verified against
the cited verdict files before writing.)
