> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-06.
> Sanitised for publication: see [../README.md](../README.md).

# Ledger row 3 (client) and assumption A3

Extract of the research-phase ledger, updated 2026-10-06: its status words, row 3 and the A3 row.

Status words: PROOF (machine-checked in Lean, artifact named; PARTIAL or
CONDITIONAL when it covers part of the link or needs extra premises),
BOUNDED CHECKING (symbolic execution to stated bounds, not a proof),
CHECKED (tool runs and reading, not Lean), ASSUMPTION (named, with the
cheapest known discharge path), OPEN (not attempted or not closed). A row
marked NOT RE-CHECKABLE was checked when it landed, but its sources were
never archived.

| # | Link | Status | What is shown, and its limits |
|---|---|---|---|
| 3 | Selected client functions preserve fields, encode inputs, check guards, or route effects | PARTIAL PROOF under A3; Aeneas and Verus kept separate | At a04b8b3 all 110 relevant functions have a selected property: Aeneas 22, Verus 96 (38 new N3 mirrors, 2026-10-01), overlap 8. Of the 38 new, 4 only forward lean-imt calls; 27 check arguments and result mapping around abstract RPC, channel or process effects. Attestation-count results assume the count fits u64. Effects and production equivalence stay unproved. Astra read-judge; Claude read-judge: PASS-WITH-CORRECTIONS |
| A3 | Production libraries match the replacements and contracts used in client proofs | ASSUMPTION | Covers alloy/ruint values, ABI encoding, signing, transport, receipts and event decoding; arkworks conversions; hash, key, serde, sealring, TOML and lean-imt contracts; Tokio channels, locks and maps; filesystem, tempdir and process calls. Includes seal success, JSON append, integer serialization bounds, 64-bit words, and one fixed result per effect call. RNG inputs model supplied bytes, not entropy. No production-equivalence proof. Quote "under A3" with production claims. |
