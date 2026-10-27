// One fact, four orientations: a byte string B1 cannot equal B2 +Bytes X when B2 is not a prefix
// of B1. Each rule fires only when B1 and B2 are concrete, so the side condition evaluates.
// Soundness: if B1 ==K B2 +Bytes X, then lengthBytes(B2) <=Int lengthBytes(B1) and
// substrBytes(B1, 0, lengthBytes(B2)) ==K B2; the rules apply the contrapositive.
// Why it is needed: SafeERC20._safeTransfer compares mload(0x00) with 1 after a call that returned
// no data; memory still holds 0xa9059cbb ++ `to`, and Kontrol 1.0.255 leaves
// b"\x00..\x01" == b"\xa9\x05\x9c\xbb" +Bytes #range(#buf(32, rcp), 0, 28) undecided, so without
// this rule it explores a success that cannot happen (a call to an address with no code).
requires "foundry.md"

module BYTES-PREFIX-LEMMAS
    imports FOUNDRY

    rule ( B1:Bytes ==K B2:Bytes +Bytes _:Bytes ) => false
      requires lengthBytes(B2) <=Int lengthBytes(B1)
       andBool substrBytes(B1, 0, lengthBytes(B2)) =/=K B2
      [simplification, concrete(B1, B2)]

    rule ( B2:Bytes +Bytes _:Bytes ==K B1:Bytes ) => false
      requires lengthBytes(B2) <=Int lengthBytes(B1)
       andBool substrBytes(B1, 0, lengthBytes(B2)) =/=K B2
      [simplification, concrete(B1, B2)]

    rule { B1:Bytes #Equals B2:Bytes +Bytes _:Bytes } => #Bottom
      requires lengthBytes(B2) <=Int lengthBytes(B1)
       andBool substrBytes(B1, 0, lengthBytes(B2)) =/=K B2
      [simplification, concrete(B1, B2)]

    rule { B2:Bytes +Bytes _:Bytes #Equals B1:Bytes } => #Bottom
      requires lengthBytes(B2) <=Int lengthBytes(B1)
       andBool substrBytes(B1, 0, lengthBytes(B2)) =/=K B2
      [simplification, concrete(B1, B2)]
endmodule
