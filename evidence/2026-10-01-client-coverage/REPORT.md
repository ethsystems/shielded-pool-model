> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-01 (run 2026-09-30).
> Sanitised for publication: see [../README.md](../README.md).

N3 client coverage report

[checked] All 38 former class C functions now have selected properties checked on reviewed Verus mirrors. Four results only check lean-imt forwarding.
[read] Production equivalence and external effects remain unproved. This result does not mean the complete client is verified.

[checked] Target: ethsystems/pocs `a04b8b38969dfc2ee64de47edee7e396454204a8`.
[checked] Start: 2026-09-30T22:43:33+08:00. End: 2026-09-30T23:14:19+08:00. Elapsed: 30.78 minutes.
[checked] Deliverables remain in this work directory. No repository writes, commits, posts or downloads were performed.

[checked] The final fresh-copy run passed with `--no-cheating`:

| Mirror | New target functions | Verus verified count |
|---|---:|---:|
| rpc.rs | 18 | 27 |
| channel.rs | 12 | 14 |
| prover.rs | 4 | 18 |
| tree.rs | 4 | 5 |
| Total | 38 | 64 |

[checked] The verified counts include helpers and main functions. All 104 negative controls failed with proof errors.
[checked] Every target has a mutated-body control and a strengthened-postcondition control. Compiler failures do not count as rejected controls.
[checked] The accepted mirrors contain no `assume`, `admit`, `assume_specification`, `uninterp` or `external_body`.
[read] This does not remove the trusted parameter contracts listed below.

[checked] Coverage arithmetic over the inherited 110 relevant functions:

| Route | Functions | Evidence status |
|---|---:|---|
| Aeneas, including overlap | 22 | [read] Inherited extraction proofs with replacements; not rerun |
| Verus, including overlap | 96 | [read] 58 inherited; [checked] 38 new mirrors |
| Both | 8 | [read] Inherited overlap |
| Aeneas only | 14 | [read] Inherited |
| Verus only | 88 | [read] 50 inherited; [checked] 38 new |
| Union with a selected result | 110 | [checked] Table arithmetic |
| No selected result | 0 | [checked] Table arithmetic |

[read] The prior report counted 56 Verus targets. A cross-family judge identified two additional reused helper mirrors: decode_path and DecryptionError::from.
[checked] Including those helpers gives 58 inherited Verus entries and eight overlaps. The inherited union remains 72.
[read] The denominator excludes low-relevance helpers and tests. For example, mint_mock_token is outside the 110-entry inventory.
[read] No Lean or Aeneas proof was run here. No new Lean theorem or production-equivalence bridge was added.
[read] Inherited results retain A3, including alloy/ruint, arkworks, hash/key, sealring, serde/JSON/TOML and lean-imt assumptions.
[read] RNG entropy, seal success, successful JSON append behavior and stated word-size premises were not reproved.

[checked] The RPC mirrors check provider/address selection, method arguments, full-width count conversion, result mapping and receipt-status handling.
[checked] The attestation mirror returns the first decoded event and copies the earlier count into its index field.
[read] ABI encoding, signing, transport, receipt authenticity and event decoding remain library assumptions.

[checked] The channel mirrors check capacity arguments, map-key operations, message fields and receive/send result mapping.
[checked] The composition example registered_channel_cannot_send returns RecipientNotFound under the declared contracts.
[read] Source explanation: ChannelRegistry::register returns an empty cloned registry. Channel::send_note uses that returned registry.
[read] ChannelSystem is a separate implementation; its constructor retains the shared registry handle.

[checked] The prover mirrors check witness guards, proof-field placement, exact command arguments and result routing through explicit cleanup failure.
[checked] The bb arguments contain `--write_vk`, `-t`, `evm`, the circuit JSON path, witness.gz path and output directory.
[checked] Both process requests pass the package directory and `kill_on_drop(true)` to the abstract process API.
[read] Those argument facts do not prove OS process killing, directory isolation, implicit Drop cleanup or generated-proof validity.
[read] The contracts specify returned results. They do not specify effect traces or prove absence of redundant external calls.

[checked] The four tree mirrors preserve the original one-line delegated calls and pass paired controls.
[read] Their successor-state and root functions are abstract. All substantive insertion, hashing and root semantics remain with lean-imt.
[read] These four entries add forwarding breadth only. Counting them follows the earlier thin-wrapper coverage convention.

[checked] Two minimal probes establish that this cached Verus accepts async functions and concrete await calls.
[checked] A minimal async-trait probe fails with: `Verus does not yet support Opaque types in trait def`.
[read] The mirrors retain async wrappers and replace effect trait awaits with synchronous parameter calls.
[read] This checks local completed-call behavior. It does not check scheduling, cancellation or liveness.
[read] No claim of a general async impossibility or an upstream bug is made.

[read] Eight parameter interfaces contain 29 abstract spec declarations and 31 executable method contracts:

| Interface | Remaining trusted behavior |
|---|---|
| rpc::RpcApi | ABI calls, transaction submission, receipt retrieval and decoded logs |
| rpc::Setup | Key/URL parsing, signer address, wallet/provider construction |
| channel::Effects | Channel endpoints, send outcomes and receive outcomes |
| channel::RegistryApi | Map operations, empty-map creation and shared-handle identity |
| prover::Effects | TOML text and generated proof bytes, under explicit formatting bounds |
| prover::Paths | Path joins, named path components and display bytes |
| prover::Process | Filesystem results, temporary directories, process output and explicit close |
| tree::LeanImt | Abstract insertion successor and root value |

[read] These interfaces describe observations for one invocation. They do not assert deterministic behavior across live invocations.
[read] Actual libraries must satisfy the chosen contracts for a production claim. No implementation-equivalence proof is supplied.
[read] Other substitutions include fixed-width data records, flattened proof records, opaque error payloads, and sequential lock-held registry operations.
[read] Error strings, allocation failure, concurrent post-state persistence and implicit destruction remain outside the claims.
[checked] TRUSTED.md archives every interface verbatim. REVIEW.md documents all substitution classes.
[read] GAPS.md gives one remaining production boundary for each of the 38 former class C functions.

[checked] The count mirror saturates get_commitment_count at u64::MAX.
[checked] get_attestation_count verifies under a fitting-response precondition. get_attestation_leaf verifies under index < 2^40.
[read] The source uses unwrap for the latter conversions. Oversized values can panic; cached ruint conversion code supports that reading.
[read] The attestation index is sampled before submission. No atomicity guarantee connects that count to the eventual insertion.
[checked] Withdraw proving preserves the full amount without an amount guard. The corresponding stronger amount-bound control fails.
[read] TOML safety still requires the previous integer bounds. This work does not remove that client boundary.

[checked] Reproduction evidence:

- `deliverable/`: 92 pinned input files, including four mirrors, all source snapshots, complete diffs, controls and run scripts.
- `fresh-reviewed/`: a copy of that directory alone; all positive checks and 104 controls passed there.
- `source/manifest.json`: SHA256 hashes for all 110 source regions, checked against the pinned git source.
- `targets.json`: all 38 new target mappings, full hashes and paired control IDs.
- `coverage.py --check`: checks the table and complete diff contents, including the prior judge's requested correction.
- `regen-check/`: all generators reproduced the archived inputs byte for byte.
- `toolchain.json`: pinned Verus, rust_verify, vstd and solver hashes.

[checked] Verus version: 0.2026.09.13.671956e. Rust toolchain: 1.98.1-x86_64-unknown-linux-gnu.
[checked] Final verifier wall-time sum: 70.839 seconds. Scope memory peak: 1,044,574,208 bytes.
[checked] The launcher supplied a 2 GiB background.slice cap, below the brief's 4 GiB maximum. Every check stayed in that existing scope.
[checked] No permission or sandbox denial blocked this run.

[read] Re-run from the archive inside a capped background.slice scope:

```sh
./run.sh "$VERUS_DIR" "$RUSTUP_HOME"
```

[read] Optional argument three names the source repository for an additional read-only git comparison. The archive works without it.
[checked] Archive SHA256: `a619559ec709a1ca31495febd556ec8657ebb5af0de0c7c1e48c6f8c27cb8e55`.

[read] Recommendation: retain separate Aeneas and Verus counts, and label these results as selected properties under explicit contracts.
[read] Review the ChannelRegistry clone behavior first. Then address fallible RPC conversions and the pre-submission attestation index.
[read] More assurance requires dependency proofs, production correspondence or integration checks. More forwarding counts will not supply those guarantees.
[read] The deliverable is ready for the controller's independent judge and landing review.

The complete 110-row table follows. [checked] Rows, source locations and arithmetic are generated. [read] Prior proof results remain inherited.

| # | Function | File:line | Covered by | Result or reason |
|---|---|---|---|---|
| 1 | `format_field` | `adapters/bb_prover.rs:33` | Verus | [read] Prior selected property: "0x" + 64 lowercase hex digits of the word; injective (lemma) |
| 2 | `format_field_from_address` | `adapters/bb_prover.rs:38` | Verus | [read] Prior selected property: hex field of 12 zero bytes + the 20 address bytes |
| 3 | `format_u256` | `adapters/bb_prover.rs:44` | Verus | [read] Prior selected property: canonical decimal string of the FULL U256 value (no range check; >= 2^128 gives 39+ digits) |
| 4 | `pad_field_array` | `adapters/bb_prover.rs:49` | Verus | [read] Prior selected property: exactly max_depth hex fields: path zero-padded, TRUNCATED when longer |
| 5 | `pad_index_array` | `adapters/bb_prover.rs:56` | Verus | [read] Prior selected property: exactly max_depth bytes: zero-padded, TRUNCATED when longer |
| 6 | `DepositProverInput::from` | `adapters/bb_prover.rs:81` | Verus | [read] Prior selected property: all 14 fields from the right witness fields and encodings; paths padded to 20 |
| 7 | `TransferProverInput::from` | `adapters/bb_prover.rs:139` | Verus | [read] Prior selected property: all 27 fields from the right note/index/proof; paths padded to 32 |
| 8 | `WithdrawProverInput::from` | `adapters/bb_prover.rs:193` | Verus | [read] Prior selected property: all 10 fields from the right witness fields; salt from the note |
| 9 | `BBProver::format_deposit_prover_toml` | `adapters/bb_prover.rs:263` | Verus | [read] Prior selected property: Safe under the stated integer bounds and the assumed TOML contract; record provenance checked, text abstract. |
| 10 | `BBProver::format_transfer_prover_toml` | `adapters/bb_prover.rs:269` | Verus | [read] Prior selected property: Safe under the stated integer bounds and the assumed TOML contract; record provenance checked, text abstract. |
| 11 | `BBProver::format_withdraw_prover_toml` | `adapters/bb_prover.rs:275` | Verus | [read] Prior selected property: Safe under the stated integer bounds and the assumed TOML contract; record provenance checked, text abstract. |
| 12 | `BBProver::prove_circuit` | `adapters/bb_prover.rs:281` | Verus | [checked] Exact nargo/bb argument bytes and control-flow result under path/I/O/process contracts; cleanup failure propagates. |
| 13 | `BBProver::prove_deposit` | `adapters/bb_prover.rs:362` | Verus | [checked] Amount guard and proof fields under safe TOML bounds and prover contract. |
| 14 | `BBProver::prove_transfer` | `adapters/bb_prover.rs:387` | Verus | [checked] Amount/token guard outcomes and proof fields under safe TOML bounds and prover contract. |
| 15 | `BBProver::prove_withdraw` | `adapters/bb_prover.rs:415` | Verus | [checked] Proof fields under safe TOML bounds and prover contract; no amount guard. |
| 16 | `ChannelRegistry::register` | `adapters/channel.rs:47` | Verus | [checked] Capacity 100; key-to-sender insertion; returned receiver/key; cloned registry is empty. |
| 17 | `ChannelRegistry::unregister` | `adapters/channel.rs:64` | Verus | [checked] Remove exactly the selected serialized key under the sequential registry contract. |
| 18 | `ChannelRegistry::send_to` | `adapters/channel.rs:71` | Verus | [checked] Lookup key; missing recipient, send success and closed-channel mapping. |
| 19 | `ChannelRegistry::clone` | `adapters/channel.rs:94` | Verus | [checked] Return an empty registry, independent of the input entries. |
| 20 | `Channel::new` | `adapters/channel.rs:116` | Verus | [checked] Capacity 1; retain key and registry; return receiver endpoint. |
| 21 | `Channel::send_note` | `adapters/channel.rs:133` | Verus | [checked] Message fields and recipient routing to the given registry. |
| 22 | `Channel::receive_note` | `adapters/channel.rs:147` | Verus | [checked] Message to Some, Empty to None, Disconnected to ChannelClosed. |
| 23 | `Channel::receive_note_blocking` | `adapters/channel.rs:156` | Verus | [checked] Some message preserved; None becomes ChannelClosed. |
| 24 | `ChannelSystem::create_channel` | `adapters/channel.rs:176` | Verus | [checked] Capacity 100; insert chosen key/sender; retain shared handle and receiver. |
| 25 | `SystemChannel::send_note` | `adapters/channel.rs:214` | Verus | [checked] Recipient key and message fields; lookup/send error mapping. |
| 26 | `SystemChannel::receive_note` | `adapters/channel.rs:238` | Verus | [checked] Message to Some, Empty to None, Disconnected to ChannelClosed. |
| 27 | `SystemChannel::receive_note_blocking` | `adapters/channel.rs:247` | Verus | [checked] Some message preserved; None becomes ChannelClosed. |
| 28 | `EthereumRpc::new` | `adapters/ethereum_rpc.rs:120` | Verus | [checked] Signer and URL parse error categories; provider, wallet address and configured contract fields. |
| 29 | `EthereumRpc::convert_receipt` | `adapters/ethereum_rpc.rs:163` | Verus | [read] Prior selected property: fields kept; missing block number becomes 0; success = status |
| 30 | `EthereumRpc::get_commitment_root` | `adapters/ethereum_rpc.rs:176` | Verus | [checked] Provider, pool address and commitmentRoot request; Contract error mapping. |
| 31 | `EthereumRpc::get_commitment_count` | `adapters/ethereum_rpc.rs:186` | Verus | [checked] Provider and request; full U256 conversion saturates at u64::MAX. |
| 32 | `EthereumRpc::is_nullifier_spent` | `adapters/ethereum_rpc.rs:198` | Verus | [checked] Provider, pool and nullifier argument; Boolean/error forwarding. |
| 33 | `EthereumRpc::is_known_root` | `adapters/ethereum_rpc.rs:208` | Verus | [checked] Provider, pool and root argument; Boolean/error forwarding. |
| 34 | `EthereumRpc::is_token_supported` | `adapters/ethereum_rpc.rs:218` | Verus | [checked] Provider, pool and token argument; Boolean/error forwarding. |
| 35 | `EthereumRpc::get_attestation_root` | `adapters/ethereum_rpc.rs:230` | Verus | [checked] Provider, registry and root request; word/error forwarding. |
| 36 | `EthereumRpc::get_attestation_count` | `adapters/ethereum_rpc.rs:241` | Verus | [checked] Exact count under the explicit U256-to-u64 fit precondition. |
| 37 | `EthereumRpc::get_attestation_leaf` | `adapters/ethereum_rpc.rs:254` | Verus | [checked] Exact index argument under index < 2^40; result/error forwarding. |
| 38 | `EthereumRpc::is_authorized_attester` | `adapters/ethereum_rpc.rs:265` | Verus | [checked] Provider, registry and attester argument; Boolean/error forwarding. |
| 39 | `EthereumRpc::deposit` | `adapters/ethereum_rpc.rs:281` | Verus | [checked] All six ABI arguments and provider/target; send and receipt errors; status check. |
| 40 | `EthereumRpc::transfer` | `adapters/ethereum_rpc.rs:315` | Verus | [checked] Proof, ordered pairs, root and encrypted bytes; send and receipt errors; status check. |
| 41 | `EthereumRpc::withdraw` | `adapters/ethereum_rpc.rs:349` | Verus | [checked] Proof, nullifier, token, full amount, recipient and root; error/status handling. |
| 42 | `EthereumRpc::add_attester` | `adapters/ethereum_rpc.rs:387` | Verus | [checked] Registry and attester argument; send and receipt errors; status check. |
| 43 | `EthereumRpc::add_attestation` | `adapters/ethereum_rpc.rs:409` | Verus | [checked] Count before send; first decoded event fields and earlier count index; all local errors. |
| 44 | `EthereumRpc::add_supported_token` | `adapters/ethereum_rpc.rs:461` | Verus | [checked] Pool and token argument; send and receipt errors; status check. |
| 45 | `EthereumRpc::approve_token` | `adapters/ethereum_rpc.rs:487` | Verus | [checked] Token contract, pool spender and full amount; error/status handling. |
| 46 | `EthereumRpc::get_token_balance` | `adapters/ethereum_rpc.rs:510` | Verus | [checked] Token contract and account argument; full U256/error forwarding. |
| 47 | `PoseidonHash::hash` | `adapters/merkle_tree.rs:36` | Verus | [read] Prior selected property: node = h2(left mod r, right mod r) mod r, left = bytes 0..32; no panic for 64-byte input |
| 48 | `decode_path` | `adapters/merkle_tree.rs:58` | both | [read] Prior selected property: LSB-first bits, length (path_len <= usize bits) |
| 49 | `CommitmentTree::insert` | `adapters/merkle_tree.rs:77` | Verus | [checked] THIN: forward insert to lean-imt under its abstract contract; no tree semantics proved. |
| 50 | `CommitmentTree::root` | `adapters/merkle_tree.rs:92` | Verus | [checked] THIN: forward root to lean-imt under its abstract contract; no tree semantics proved. |
| 51 | `CommitmentTree::generate_commitment_proof` | `adapters/merkle_tree.rs:97` | Verus | [read] Prior selected property: None iff lean-imt errs; path = siblings in order; bits from the PROOF index (not leaf_index); leaf_index kept; length = sibling count |
| 52 | `AttestationTree::insert` | `adapters/merkle_tree.rs:135` | Verus | [checked] THIN: forward insert to lean-imt under its abstract contract; no tree semantics proved. |
| 53 | `AttestationTree::root` | `adapters/merkle_tree.rs:150` | Verus | [checked] THIN: forward root to lean-imt under its abstract contract; no tree semantics proved. |
| 54 | `AttestationTree::generate_attestation_proof` | `adapters/merkle_tree.rs:155` | Verus | [read] Prior selected property: as generate_commitment_proof |
| 55 | `b256_to_bytes` | `adapters/merkle_tree.rs:187` | Verus | [read] Prior selected property: bytes kept |
| 56 | `bytes_to_b256` | `adapters/merkle_tree.rs:192` | Verus | [read] Prior selected property: bytes kept; from_slice cannot panic |
| 57 | `NoteDomain::encode_note` | `crypto/encryption.rs:45` | Verus | [read] Prior selected property: appends J::json(note) to out on Ok |
| 58 | `NoteDomain::decode_note` | `crypto/encryption.rs:49` | Verus | [read] Prior selected property: result = J::decoded(bytes) |
| 59 | `encrypt_note` | `crypto/encryption.rs:55` | Verus | [read] Prior selected property: bytes = sealring envelope for (recipient key, note, EMPTY AAD, RNG); no panic under the seal premise |
| 60 | `decrypt_note` | `crypto/encryption.rs:72` | Verus | [read] Prior selected property: Ok only if parse succeeds and open returns Some; error mapping exact; AAD empty |
| 61 | `DecryptionError::from` | `crypto/encryption.rs:97` | both | [read] Prior selected property: exhaustive OpenError mapping |
| 62 | `b256_to_fr` | `crypto/poseidon.rs:13` | Verus | [read] Prior selected property: field value = big-endian value mod r (BN254 scalar) |
| 63 | `fr_to_b256` | `crypto/poseidon.rs:18` | Verus | [read] Prior selected property: 32 big-endian bytes of the canonical value (< r); from_slice never panics |
| 64 | `poseidon1` | `crypto/poseidon.rs:26` | Verus | [read] Prior selected property: output = h1(key mod r) mod r, canonical; both expect calls cannot fail |
| 65 | `poseidon2` | `crypto/poseidon.rs:40` | Verus | [read] Prior selected property: output = h2(a mod r, b mod r) mod r, argument order a, b; no panic |
| 66 | `poseidon4` | `crypto/poseidon.rs:54` | Verus | [read] Prior selected property: output = h4(a, b, c, d mod r) mod r, order kept; no panic |
| 67 | `Commitment::nullifier` | `domain/commitment.rs:41` | Verus | [read] Prior selected property: H2 order |
| 68 | `payload_commitment` | `domain/commitment.rs:51` | Verus | [read] Prior selected property: output = keccak(payload) mod r as 32 big-endian bytes, canonical |
| 69 | `EncryptedNote::from_bytes` | `domain/encrypted.rs:37` | Verus | [read] Prior selected property: empty rejected, bytes kept (Verus detour) |
| 70 | `P2pMessage::new` | `domain/encrypted.rs:62` | Verus | [read] Prior selected property: fields kept; no validation (empty ciphertext accepted) |
| 71 | `EncryptedTransferNotes::new` | `domain/encrypted.rs:87` | Aeneas | [read] Prior selected property: positions kept |
| 72 | `EncryptedTransferNotes::to_bytes` | `domain/encrypted.rs:92` | both | [read] Prior selected property: BE32 prefix + payloads (capacity premise); Verus roundtrip |
| 73 | `EncryptedTransferNotes::from_bytes` | `domain/encrypted.rs:104` | Verus | [read] Prior selected property: exact split and errors (Verus detour, 64-bit) |
| 74 | `SpendingKey::random` | `domain/keys.rs:18` | Verus | [read] Prior selected property: key < 2^216 < r |
| 75 | `SpendingKey::from_bytes` | `domain/keys.rs:26` | Aeneas | [read] Prior selected property: byte preservation |
| 76 | `SpendingKey::derive_owner_pubkey` | `domain/keys.rs:32` | Verus | [read] Prior selected property: H1(key) |
| 77 | `OwnerPubkey::from_bytes` | `domain/keys.rs:49` | Aeneas | [read] Prior selected property: byte preservation |
| 78 | `ViewingKey::random` | `domain/keys.rs:66` | Verus | [read] Prior selected property: key = k256 generator on the supplied RNG bytes |
| 79 | `ViewingKey::from_bytes` | `domain/keys.rs:71` | Verus | [read] Prior selected property: Ok exactly when k256 accepts the bytes; wraps that key |
| 80 | `ViewingKey::derive_viewing_pubkey` | `domain/keys.rs:76` | Verus | [read] Prior selected property: wraps k256 public_key of the secret |
| 81 | `ViewingPubkey::from_sec1_bytes` | `domain/keys.rs:92` | Verus | [read] Prior selected property: Ok exactly when k256 accepts the SEC1 bytes |
| 82 | `ViewingPubkey::to_sec1_bytes` | `domain/keys.rs:102` | Verus | [read] Prior selected property: bytes = COMPRESSED SEC1 encoding |
| 83 | `viewing_pubkey_serde::serialize` | `domain/keys.rs:116` | Verus | [read] Prior selected property: serializes the COMPRESSED SEC1 bytes |
| 84 | `viewing_pubkey_serde::deserialize` | `domain/keys.rs:124` | Verus | [read] Prior selected property: Deserializer errors preserved; success requires decoded bytes accepted by k256; parser-error text is unspecified. |
| 85 | `CommitmentMerkleProof::new` | `domain/merkle.rs:34` | Aeneas | [read] Prior selected property: length assignment |
| 86 | `CommitmentMerkleProof::with_proof_length` | `domain/merkle.rs:45` | Aeneas | [read] Prior selected property: preservation |
| 87 | `AttestationMerkleProof::new` | `domain/merkle.rs:76` | Aeneas | [read] Prior selected property: length assignment |
| 88 | `AttestationMerkleProof::with_proof_length` | `domain/merkle.rs:87` | Aeneas | [read] Prior selected property: preservation |
| 89 | `AttestationMerkleProof::from_contract_elements` | `domain/merkle.rs:103` | Verus | [read] Prior selected property: word bytes and index bits (Verus detour) |
| 90 | `Note::new` | `domain/note.rs:38` | Verus | [read] Prior selected property: salt < 2^216 < r, fields kept |
| 91 | `Note::with_salt` | `domain/note.rs:52` | Aeneas | [read] Prior selected property: field placement |
| 92 | `Note::zero` | `domain/note.rs:67` | Verus | [read] Prior selected property: amount 0, salt canonical |
| 93 | `Note::commitment` | `domain/note.rs:73` | Verus | [read] Prior selected property: H4 argument order and encoding |
| 94 | `Note::nullifier` | `domain/note.rs:86` | Verus | [read] Prior selected property: H2(commitment, key) |
| 95 | `Note::is_zero` | `domain/note.rs:91` | Verus | [read] Prior selected property: iff value 0 |
| 96 | `DepositProof::new` | `domain/proof.rs:34` | Aeneas | [read] Prior selected property: six fields placed |
| 97 | `DepositProof::public_inputs_as_array` | `domain/proof.rs:57` | both | [read] Prior selected property: word layout of the public inputs (Aeneas, shim); Verus full-U256 mirror for deposit/withdraw |
| 98 | `TransferProof::new` | `domain/proof.rs:91` | Aeneas | [read] Prior selected property: index and field placement |
| 99 | `TransferProof::public_inputs_as_array` | `domain/proof.rs:112` | Aeneas | [read] Prior selected property: Public-input word layout through the Aeneas extraction shim. |
| 100 | `TransferProof::nullifiers` | `domain/proof.rs:124` | Aeneas | [read] Prior selected property: ordered pair |
| 101 | `TransferProof::output_commitments` | `domain/proof.rs:132` | Aeneas | [read] Prior selected property: ordered pair |
| 102 | `WithdrawProof::new` | `domain/proof.rs:161` | Aeneas | [read] Prior selected property: five fields placed |
| 103 | `WithdrawProof::public_inputs_as_array` | `domain/proof.rs:182` | both | [read] Prior selected property: word layout of the public inputs (Aeneas, shim); Verus full-U256 mirror for deposit/withdraw |
| 104 | `DepositWitness::new` | `domain/witness.rs:61` | Verus | [read] Prior selected property: 13-field provenance |
| 105 | `DepositWitness::validate_amount` | `domain/witness.rs:90` | Verus | [read] Prior selected property: iff 0 < amount < 2^128 |
| 106 | `TransferWitness::new` | `domain/witness.rs:121` | Verus | [read] Prior selected property: index and field provenance |
| 107 | `TransferWitness::validate_amounts` | `domain/witness.rs:155` | both | [read] Prior selected property: accepts iff 4 amounts and both sums < 2^128 and equal |
| 108 | `TransferWitness::sum` | `domain/witness.rs:156` | both | [read] Prior selected property: exact checked sum (Aeneas `sum_spec`; Verus) |
| 109 | `TransferWitness::validate_token_consistency` | `domain/witness.rs:168` | both | [read] Prior selected property: all tokens equal |
| 110 | `WithdrawWitness::new` | `domain/witness.rs:202` | Verus | [read] Prior selected property: nullifier and field provenance |
