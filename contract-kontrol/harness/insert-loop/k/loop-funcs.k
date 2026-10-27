// Specification functions for the LeanIMT._insert loop (InternalLeanIMT.sol:65-75),
// for SELF = 0 (the tree at slot 0) and the PoseidonT3 keccak stub. These are definitions, not
// lemmas: each rule is one case of the Solidity loop body. The requires use the exact branch
// conditions the prover produces at pc 1972 (loop test) and pc 1986 (bit test).
requires "foundry.md"

module LOOP-FUNCS
    imports FOUNDRY

    // sideNodes[L] slot for a LeanIMTData at slot 0: keccak(L ++ 2)
    syntax Int ::= #snKey ( Int ) [function, total]
    rule #snKey(L) => keccak(#buf(32, L) +Bytes #buf(32, 2))

    // PoseidonT3Stub.hash([A, B]) = keccak(A ++ B) mod F
    syntax Int ::= #stubH ( Int , Int ) [function, total]
    rule #stubH(A, B) => keccak(#buf(32, A) +Bytes #buf(32, B)) modInt 21888242871839275222246405745257275088548364400416034343698204186575808495617

    // node after the loop, from level L with node N
    syntax Int ::= #lnode ( Map , Int , Int , Int , Int ) [function, total]
    rule #lnode(_S, L, D, _I, N) => N requires D <=Int L
    rule #lnode(S, L, D, I, N) => #lnode(S, L +Int 1, D, I, #stubH(#lookup(S, #snKey(L)), N))
      requires L <Int D andBool 0 ==Int chop(1 -Int (1 &Int (I >>Int L)))
    rule #lnode(S, L, D, I, N) => #lnode(S [ #snKey(L) <- N ], L +Int 1, D, I, N)
      requires L <Int D andBool notBool 0 ==Int chop(1 -Int (1 &Int (I >>Int L)))

    // storage after the loop
    syntax Map ::= #lstore ( Map , Int , Int , Int , Int ) [function, total]
    rule #lstore(S, L, D, _I, _N) => S requires D <=Int L
    rule #lstore(S, L, D, I, N) => #lstore(S, L +Int 1, D, I, #stubH(#lookup(S, #snKey(L)), N))
      requires L <Int D andBool 0 ==Int chop(1 -Int (1 &Int (I >>Int L)))
    rule #lstore(S, L, D, I, N) => #lstore(S [ #snKey(L) <- N ], L +Int 1, D, I, N)
      requires L <Int D andBool notBool 0 ==Int chop(1 -Int (1 &Int (I >>Int L)))
endmodule
