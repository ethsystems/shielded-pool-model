# Concrete witnesses

[checked] All numbers are unsigned integers. All unlisted storage slots start at zero.
Let `H(a,b) = uint256(keccak256(abi.encode(a,b))) mod F`.
`F = 21888242871839275222246405745257275088548364400416034343698204186575808495617`.

`RA = H(102,11) = 4704717579518918221835877255356199702159254264878076234632567839161174709242`.

`RB = H(103,13) = 2226215065757261591238298848758084862258130908540212829429346428046868354252`.

| Witness | DEPTH | LEVEL at entry | INDEX | NODE at entry | LEAF | Visited bits |
|---|---:|---:|---:|---|---:|---|
| M1-A | 2 | 0 | 2 | 11 | 11 | level 0: 0; level 1: 1 |
| M1-B | 4 | 1 | 5 | 13 | 13 | level 1: 0; level 2: 1; level 3: 0 |
| M2-A | 2 | 0 | 2 | 11 | 11 | level 0: 0; level 1: 1 |
| M2-B | 4 | 1 | 5 | 13 | 13 | level 1: 0; level 2: 1; level 3: 0 |
| M3-A | 2 | 2 | 2 | RA | 11 | none: post-loop entry |
| M3-B | 4 | 4 | 5 | RB | 13 | none: post-loop entry |

[checked] Each witness starts with `S[0]=9`, `S[1]=17`, and `sideNodes[i]=101+i` for `i=0..4`.
Also, `leaves[i]=701+i` for `i=0..4`, `sideNodes[LEAF]=800+LEAF`, and `leaves[LEAF]=0`.
Two extra sentinels are `S[77]=177` and `S[keccak(abi.encode(88,105))]=188`.
The 16 specified storage keys are distinct in both witnesses.

[checked] `A5=0`, `SELF=0`, and `FMP=128` in the archived runtime entry adapter.
For `loop-frame2`, `(K,M)=(0,3)` at depth 2 and `(1,3)` at depth 4; `WS` is empty.
For `loop-frame` and `loop-exact`, the same physical stack uses `WS=[initial LEVEL,3]`.
For `post-loop-exact`, the return address is 369 and `WS` is empty.

| Mutant | Rejected postcondition | Stock A | Mutant A | Stock B | Mutant B |
|---|---|---|---|---|---|
| M1 | loop-frame: slot 0 unchanged | 9 | 11 | 9 | RB |
| M2 | loop-frame2: selected leaves key unchanged | leaves[0]=701 | leaves[0]=11 | leaves[1]=702 | leaves[1]=13 |
| M3 | post-loop-exact: leaves[LEAF]=INDEX+1 | leaves[11]=3 | leaves[11]=0 | leaves[13]=6 | leaves[13]=0 |
| M1, M2 | loop-exact: first visited side node updated | sideNodes[0]=11 | sideNodes[0]=101 | sideNodes[1]=13 | sideNodes[1]=102 |

[checked] M3 also changes `sideNodes[11]` from 811 to 3, or `sideNodes[13]` from 813 to 6.
Stock preserves those entries. Both implementations return RA or RB and correctly write the separate root entry.

[checked] Both loops include a hash branch and a zero-bit branch. INDEX is never the all-ones word.
The loop memory bounds are `128+96*2=320` and `128+96*3=416`, both below `2^32`.
M3 has `INDEX+1=3` or `6`, both below `2^256`.

[checked] `witnesses.json` gives numeric keys, complete finite storage maps, branch traces, and both final maps.
`tools/check_witnesses.py` computes these maps independently and checks all 40 Foundry observations.
