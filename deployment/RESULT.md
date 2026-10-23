# RESULT: the Sepolia deployment against a fresh build of `a04b8b3`

Run on 2026-10-23, from 12:23 to 12:27 UTC, on a Linux x86_64 laptop (16 threads, btrfs).
The checker files are those of commit `7bda88c` of this repo:

```
1aa7f3d2d7df53b377215fb10f575cdfb0d216a89924eb3f4265e329aed107e9  check.sh
2c96fc0e4197447e03baa4809915a56cadbc44bdf2e9c4dc1ce18bb29e88430e  PINS.txt
327931683b214368f68181225d024365aa858714996445a61d19fd3a86342cfc  scripts/deploy-check.py
81b1378ce85e696b41ecd1b440714371c438bca22a885117f4d9dc6390d85a91  scripts/recheck-deploy.sh
61b2fc1ddb53b2c650923e6179399610decc084a11bd5675500e3ad4317b4943  scripts/soldeer-integrity.py
2f0645275f070a4596a27abd6ab05ef4d886368eb0c009b48c20f59637f70d29  claims/sepolia-2026-10-23.json
75c07bf32fb0a93a20659a38deef86211a82fe9b2672976312d4cab671eef52b  claims/sepolia.json
```

Tools: forge and cast 1.8.3 (`cae51ad4`), solc 0.8.37+commit.f401782d, all three with the
binary sha256 in `PINS.txt` (the Linux x86_64 release builds). The build ran under
`unshare -rn`, in a network namespace with no network.

In the logs below, `<checkout>` stands for the path of the checkout and `<foundry>` for the
directory of forge and cast; `~` is the home directory. Nothing else is changed.

## Summary

| Claim | Block | RPC | Verdict |
|---|---|---|---|
| `claims/sepolia.json` | 11949456 | `https://sepolia.drpc.org`, `LOG_WINDOW=100` | PASS, 32 of 32 CHECK lines, no WARN |
| `claims/sepolia-2026-10-23.json` | 11976486 | `https://sepolia.drpc.org`, `LOG_WINDOW=100` | PASS, 32 of 32 CHECK lines, no WARN |
| `claims/sepolia.json` | 11949456 | `https://sepolia.gateway.tenderly.co` | PASS, 32 of 32, no WARN |
| `claims/sepolia-2026-10-23.json` | 11976486 | `https://sepolia.gateway.tenderly.co` | PASS, 32 of 32, no WARN |
| `claims/sepolia.json` | 11949456 | `https://ethereum-sepolia-rpc.publicnode.com` | no verdict: the RPC has no state at that block |
| `claims/sepolia-2026-10-23.json` | 11976486 | `https://ethereum-sepolia-rpc.publicnode.com` | no verdict: the RPC has no state at block 11948522 for the log guard |

Block 11949456 is the block of the last deployment transaction, the block the writeup
names for the run of 2026-10-19. Block 11976486 was a finalized block on 2026-10-23.
`https://sepolia.drpc.org`, `https://sepolia.gateway.tenderly.co` and
`https://ethereum-sepolia-rpc.publicnode.com` gave the same hash for it. drpc refuses
`eth_getLogs` over more than about 100 blocks (its error text says 10000), so its runs set
`LOG_WINDOW=100`. Tenderly answers each window of 10000 blocks in one query.
`https://rpc.sepolia.org` did not answer (HTTP 522).

No line is a WARN. The 12 METADATA lines pass: each CBOR tail, with the ipfs hash of the
metadata, equals that of the rebuild, so the pool's metadata does not carry library addresses
(the case that gives a METADATA WARN on the pool, see README.md).

## Primary run: block 11949456, drpc

```
$ env LOG_WINDOW=100 ./check.sh https://sepolia.drpc.org claims/sepolia.json
start 2026-10-23 12:23:01 UTC
tools: forge and cast 1.8.3 (<foundry>/forge, <foundry>/cast), solc 0.8.37+commit.f401782d (~/.local/share/svm/0.8.37/solc-0.8.37)
source: pocs a04b8b38969dfc2ee64de47edee7e396454204a8, 16 files under pocs/private-payment/shielded-pool equal the blob pins
deps: @openzeppelin-contracts-5.6.0-rc.1 zip sha256 d37187263f82783c5eaeeb3c18d0147e23d54ae33f5966fce2a7bac60ce81480
deps: forge-std-1.14.0 zip sha256 d10079d1b7aac1a36dd2eeb4c5d042e8ed27b00f4ef89530b7f0a6ecd18cada3
deps: poseidon-solidity-0.0.5 zip sha256 c622cf4f348014da6947d3ddeba267317f1ca3701466f92e0be64a7726c3b31c
deps: zk-kit.solidity a171c845ec7fdc50cdd1fe96c14c27d707cdfbed tree 7ced94aea59a00e9b53fe8eaf36fa849f0ba79cd
rpc=https://sepolia.drpc.org claim=<checkout>/deployment/claims/sepolia.json sha256=75c07bf32fb0a93a20659a38deef86211a82fe9b2672976312d4cab671eef52b
pocs=<checkout>/deployment/pocs pin=a04b8b38969dfc2ee64de47edee7e396454204a8
export: 16 files, blob ids equal git ls-tree a04b8b38969dfc2ee64de47edee7e396454204a8 (export-manifest.txt)
zk-kit: archive of a171c845ec7fdc50cdd1fe96c14c27d707cdfbed, tree 7ced94aea59a00e9b53fe8eaf36fa849f0ba79cd
@openzeppelin-contracts-5.6.0-rc.1: integrity 964d6bbaf7ea075943d73945a3263e4d098ca7597978a296be48cbe1a792eb85 lock 964d6bbaf7ea075943d73945a3263e4d098ca7597978a296be48cbe1a792eb85 OK
forge-std-1.14.0: integrity 64133846def1b04b1726d2bf1292c19050a0e8cb832b60c6104c19595b9699f8 lock 64133846def1b04b1726d2bf1292c19050a0e8cb832b60c6104c19595b9699f8 OK
poseidon-solidity-0.0.5: integrity fecc3410994eebc6edf14e86fd388c31d8095c4abbba4a5772e5287f381df2fd lock fecc3410994eebc6edf14e86fd388c31d8095c4abbba4a5772e5287f381df2fd OK
zk-kit-v1: git dependency, rev a171c845ec7fdc50cdd1fe96c14c27d707cdfbed
build: (cd <checkout>/deployment/work/sepolia/ref && unshare -rn forge build --offline --build-info --use ~/.local/share/svm/0.8.37/solc-0.8.37)
build exit=0; Compiling 49 files with Solc 0.8.37 Solc 0.8.37 finished in 3.32s 
REF build-info=688eefcf2a7b4257.json solc=0.8.37 sources=49 optimizer={'enabled': True, 'runs': 100} evm=osaka
REF settings viaIR=False evmVersion=osaka metadata={'useLiteralContent': False, 'bytecodeHash': 'ipfs', 'appendCBOR': True}
CHECK CHAIN PASS chainId=11155111 head=11976642 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 claimed chainId=11155111 block=11949456 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 (the RPC and its history are trusted)
CHECK CODE:pool PASS 0xabefb40982e399f979cfdc712e57e334ea2b10ea 6266 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:pool PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:composite PASS 0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548 1441 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:composite PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:registry PASS 0xe64018ba103846d7b09b3cb2a8ac06384196b0ba 2337 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:registry PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:depositVerifier PASS 0x8f43176beb45505c0b80e0b115f91a1e7b1113fc 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:depositVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:transferVerifier PASS 0x0283b13dc7af959449d8344de3caa6c0deeb90ff 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:transferVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:withdrawVerifier PASS 0xfe5811d3a1918553027f428f56d427fb28c9def6 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:withdrawVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:depositTranscriptLib PASS 0x3cba008e48a098017a4b331f514d5b83a16cdeac 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:depositTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:transferTranscriptLib PASS 0x5045ed70c25d12da730f11a0f6d80249ebca152b 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:transferTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:withdrawTranscriptLib PASS 0x7cd19aac2cc4491568c93609ad50ba9bb675f48a 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:withdrawTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:leanIMT PASS 0x38b16dae55fefb3198b470e6559f76560c0cce19 4332 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:leanIMT PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:poseidonT3 PASS 0x72b98a5fff1dd0e7001a6327b5b99d256ebd1ce8 16413 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:poseidonT3 PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:poseidonT5 PASS 0x889010cdd13ee425bd7246e05fe872183b3cc39f 16347 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:poseidonT5 PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK SLOTS PASS deposit, transfer, withdraw slots hold the claimed verifiers with their own VK_HASH deposit=0x21cba1cbaf0dfc979b5978d694f7c2bedf98ef8012139a33e3218132e642230d, transfer=0x0ff59d91add8bc788eec2e2900e4ec1a9a726bb135c268842be11ab45a5eeb4d, withdraw=0x0c9e8ed785da4796fe241839bab23899dd7a4dc2723faa4db3b9fbd9e6183cfc
CHECK MOCK PASS no mock code at pool.verifier() or any composite slot (4 addresses compared with MockVerifier and MockCompositeVerifier)
CHECK WIRING PASS pool.verifier()=0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548, registry=0xe64018ba103846d7b09b3cb2a8ac06384196b0ba
LOGS pool blocks 11948523..11949456: 1 logs {'OwnershipTransferred': 1}; pool code at block 11948522: 0 bytes
CHECK EVENTS PASS no VerifierUpdated log in blocks 11948523..claimed block (no pool code before them)
CHECK OWNER PASS owner()=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906 claimed=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906 OwnershipTransferred logs=1 last new owner=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906
CHECK TOKENS PASS from logs=[] claimed=[] supportedTokens()={}
CHECK CHAIN-END PASS chain state at end (11155111, 11976642, '0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60'), at start (11155111, 11976642, '0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60') (chain id and hash at block 11949456 unchanged, head not lower)
VERDICT PASS failing=[] warnings=[]
deploy-check exit=0
check.sh: exit 0, out-dir <checkout>/deployment/work/sepolia, 11s
exit 0
end 2026-10-23 12:23:12 UTC
```

## Second run: block 11976486, drpc

```
$ env LOG_WINDOW=100 ./check.sh https://sepolia.drpc.org claims/sepolia-2026-10-23.json
start 2026-10-23 12:23:12 UTC
build exit=0; Compiling 49 files with Solc 0.8.37 Solc 0.8.37 finished in 2.86s 
REF build-info=6155701fcb48d564.json solc=0.8.37 sources=49 optimizer={'enabled': True, 'runs': 100} evm=osaka
REF settings viaIR=False evmVersion=osaka metadata={'useLiteralContent': False, 'bytecodeHash': 'ipfs', 'appendCBOR': True}
CHECK CHAIN PASS chainId=11155111 head=11976643 hash=0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd claimed chainId=11155111 block=11976486 hash=0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd (the RPC and its history are trusted)
CHECK CODE:pool PASS 0xabefb40982e399f979cfdc712e57e334ea2b10ea 6266 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:pool PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:composite PASS 0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548 1441 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:composite PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:registry PASS 0xe64018ba103846d7b09b3cb2a8ac06384196b0ba 2337 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:registry PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:depositVerifier PASS 0x8f43176beb45505c0b80e0b115f91a1e7b1113fc 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:depositVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:transferVerifier PASS 0x0283b13dc7af959449d8344de3caa6c0deeb90ff 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:transferVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:withdrawVerifier PASS 0xfe5811d3a1918553027f428f56d427fb28c9def6 24252 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:withdrawVerifier PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:depositTranscriptLib PASS 0x3cba008e48a098017a4b331f514d5b83a16cdeac 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:depositTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:transferTranscriptLib PASS 0x5045ed70c25d12da730f11a0f6d80249ebca152b 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:transferTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:withdrawTranscriptLib PASS 0x7cd19aac2cc4491568c93609ad50ba9bb675f48a 6081 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:withdrawTranscriptLib PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:leanIMT PASS 0x38b16dae55fefb3198b470e6559f76560c0cce19 4332 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:leanIMT PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:poseidonT3 PASS 0x72b98a5fff1dd0e7001a6327b5b99d256ebd1ce8 16413 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:poseidonT3 PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK CODE:poseidonT5 PASS 0x889010cdd13ee425bd7246e05fe872183b3cc39f 16347 bytes before metadata equal (links and immutables filled, nothing masked)
CHECK METADATA:poseidonT5 PASS CBOR tail bytes equal (53 bytes), solc 000825
CHECK SLOTS PASS deposit, transfer, withdraw slots hold the claimed verifiers with their own VK_HASH deposit=0x21cba1cbaf0dfc979b5978d694f7c2bedf98ef8012139a33e3218132e642230d, transfer=0x0ff59d91add8bc788eec2e2900e4ec1a9a726bb135c268842be11ab45a5eeb4d, withdraw=0x0c9e8ed785da4796fe241839bab23899dd7a4dc2723faa4db3b9fbd9e6183cfc
CHECK MOCK PASS no mock code at pool.verifier() or any composite slot (4 addresses compared with MockVerifier and MockCompositeVerifier)
CHECK WIRING PASS pool.verifier()=0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548, registry=0xe64018ba103846d7b09b3cb2a8ac06384196b0ba
LOGS pool blocks 11948523..11976486: 1 logs {'OwnershipTransferred': 1}; pool code at block 11948522: 0 bytes
CHECK EVENTS PASS no VerifierUpdated log in blocks 11948523..claimed block (no pool code before them)
CHECK OWNER PASS owner()=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906 claimed=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906 OwnershipTransferred logs=1 last new owner=0x53d475a7232cfaf06ff6b63c1b62b689b4db3906
CHECK TOKENS PASS from logs=[] claimed=[] supportedTokens()={}
CHECK CHAIN-END PASS chain state at end (11155111, 11976646, '0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd'), at start (11155111, 11976643, '0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd') (chain id and hash at block 11976486 unchanged, head not lower)
VERDICT PASS failing=[] warnings=[]
check.sh: exit 0, out-dir <checkout>/deployment/work/sepolia-2026-10-23, 43s
exit 0
end 2026-10-23 12:23:55 UTC
```

## Cross-check: the same claims on a second RPC

```
$ ./check.sh https://sepolia.gateway.tenderly.co claims/sepolia.json
start 2026-10-23 12:23:55 UTC
CHECK CHAIN PASS chainId=11155111 head=11976644 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 claimed chainId=11155111 block=11949456 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 (the RPC and its history are trusted)
LOGS pool blocks 11948523..11949456: 1 logs {'OwnershipTransferred': 1}; pool code at block 11948522: 0 bytes
VERDICT PASS failing=[] warnings=[]
check.sh: exit 0, out-dir <checkout>/deployment/work/sepolia, 9s
$ ./check.sh https://sepolia.gateway.tenderly.co claims/sepolia-2026-10-23.json
start 2026-10-23 12:24:04 UTC
CHECK CHAIN PASS chainId=11155111 head=11976647 hash=0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd claimed chainId=11155111 block=11976486 hash=0x0ac3f23b9652b58375cbab34c681e213e96bfb436d10526d80f499d02e7f52bd (the RPC and its history are trusted)
LOGS pool blocks 11948523..11976486: 1 logs {'OwnershipTransferred': 1}; pool code at block 11948522: 0 bytes
VERDICT PASS failing=[] warnings=[]
check.sh: exit 0, out-dir <checkout>/deployment/work/sepolia-2026-10-23, 9s
```

Every other CHECK line of the two Tenderly runs is the same PASS line as in the drpc run of
the same claim.

## An RPC without history

publicnode keeps state for about the last 10000 blocks only. At block 11949456 every
`eth_getCode` fails and the first `eth_call` stops the comparison. At block 11976486 the 12
CODE and METADATA lines, SLOTS, MOCK and WIRING pass; then the log guard asks for the pool's
code at block 11948522 and stops the comparison:

```
$ ./check.sh https://ethereum-sepolia-rpc.publicnode.com claims/sepolia.json
start 2026-10-23 12:24:13 UTC
CHECK CHAIN PASS chainId=11155111 head=11976648 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 claimed chainId=11155111 block=11949456 hash=0xe2adfa5f7a107f04fd426348301d82be3f72590440a34a0f7cf12f81ce91ea60 (the RPC and its history are trusted)
CHECK CODE:pool FAIL 0xabefb40982e399f979cfdc712e57e334ea2b10ea: RuntimeError: eth_getCode: {'code': 4444, 'message': 'pruned history unavailable: requested 11949456, earliest available 11966579'}
RuntimeError: eth_call: {'code': 4444, 'message': 'pruned history unavailable: requested 11949456, earliest available 11966570'}
VERDICT FAIL (no verdict from scripts/recheck-deploy.sh: see the lines above)
$ ./check.sh https://ethereum-sepolia-rpc.publicnode.com claims/sepolia-2026-10-23.json
start 2026-10-23 12:24:20 UTC
CHECK WIRING PASS pool.verifier()=0x6b9785df1f803c0e5bcae78dbeb8c2397a0ac548, registry=0xe64018ba103846d7b09b3cb2a8ac06384196b0ba
RuntimeError: eth_getCode: {'code': 4444, 'message': 'pruned history unavailable: requested 11948522, earliest available 11966580'}
VERDICT FAIL (no verdict from scripts/recheck-deploy.sh: see the lines above)
```

An RPC error gives no verdict and exit 1, never a PASS.

## Controls

`check.sh --controls` runs the unchanged claim, then six planted claims, each one change to
the claim file. Each must fail at exactly the named checks, with exactly the named warnings
(added to those of the unchanged claim, here none). The chain, the source and the build stay
as they are.

```
$ env LOG_WINDOW=100 ./check.sh --controls https://sepolia.drpc.org claims/sepolia.json
start 2026-10-23 12:24:29 UTC
CONTROLS ok: unchanged passes (warnings: -)
CONTROLS ok: wrong-registry fails at CODE:registry,WIRING (warnings: METADATA:registry)
CONTROLS ok: swapped-verifiers fails at CODE:composite,CODE:depositVerifier,CODE:transferVerifier,SLOTS (warnings: METADATA:depositVerifier,METADATA:transferVerifier)
CONTROLS ok: wrong-owner fails at OWNER (warnings: -)
CONTROLS ok: extra-token fails at TOKENS (warnings: -)
CONTROLS ok: wrong-block-hash fails at CHAIN (warnings: skipped)
CONTROLS ok: late-logs fails at EVENTS,OWNER (warnings: -)
CONTROLS PASS: 7 claims, 71s
end 2026-10-23 12:25:40 UTC
$ ./check.sh --controls https://sepolia.gateway.tenderly.co claims/sepolia-2026-10-23.json
start 2026-10-23 12:25:40 UTC
CONTROLS ok: unchanged passes (warnings: -)
CONTROLS ok: wrong-registry fails at CODE:registry,WIRING (warnings: METADATA:registry)
CONTROLS ok: swapped-verifiers fails at CODE:composite,CODE:depositVerifier,CODE:transferVerifier,SLOTS (warnings: METADATA:depositVerifier,METADATA:transferVerifier)
CONTROLS ok: wrong-owner fails at OWNER (warnings: -)
CONTROLS ok: extra-token fails at TOKENS (warnings: -)
CONTROLS ok: wrong-block-hash fails at CHAIN (warnings: skipped)
CONTROLS ok: late-logs fails at EVENTS,OWNER (warnings: -)
CONTROLS PASS: 7 claims, 65s
end 2026-10-23 12:26:45 UTC
```

- wrong-registry: `registry` names the deposit transcript library. CODE:registry finds other
  code there, and WIRING finds that the pool points at another registry. The METADATA WARN
  shows that the tail of other code, with the same solc, is a WARN, not a PASS.
- swapped-verifiers: the deposit and transfer verifier addresses trade places. Both CODE
  lines fail, CODE:composite fails at byte 157 (the first verifier immutable), and SLOTS
  names the `VK_HASH` each slot holds.
- wrong-owner, extra-token: `owner` and `supportedTokens` name `0x...dead`.
- wrong-block-hash: CHAIN fails and the other checks do not run.
- late-logs: the logs start at the claimed block, after the pool's creation. The guard finds
  pool code before that block (EVENTS), and the ownership log of block 11948552 is not read
  (OWNER).

A third controls run, `./check.sh --controls https://sepolia.gateway.tenderly.co
claims/sepolia.json` at 12:31 UTC, gave the same seven lines and `CONTROLS PASS: 7 claims, 67s`.

One earlier controls run on drpc stopped once with a build exit of 1 and no build log
(before the build log tail was added); the rerun passed, and it did not recur in more than
30 later builds. One run on Tenderly hit HTTP 429; `deploy-check.py` now retries 429 and 5xx. The
runs above are the first runs with the committed checker.
