-- Control (must fail to compile): the token-call conclusion of `Journey.withdraw_journey` with
-- two words swapped, the amount in the recipient slot and the recipient in the amount slot. The
-- theorem fixes the order `transfer(token, recipient, amount)`; the swapped call does not follow,
-- and rewriting with the proved token-call equation leaves the two lists unequal.
import Journey.Withdraw

namespace LeanShieldedPool.Refine.Journey

variable {P : PrimSpec}

example {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {pext : PathExt} {sup : P.Token → Prop}
    (hWP : WithdrawPost X) (hEnv : OwnerCallbackFree X)
    (hW : WithdrawRows E C) (hPF : PathFacts H E C ext pext) (hinj : Function.Injective E.cm)
    {σ σ' : Storage} {nf tok amt rcpt root : Nat} {tr : List Ext}
    (hreach : Reach X σ) (hpin : σ.verifier = X.pinnedVerifier)
    (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ')
    (hA2 : X.Verified X.pinnedVerifier .withdraw [nf, tok, amt, rcpt, root] →
      Canonical [nf, tok, amt, rcpt, root] →
      C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]))
    {n : Note P} {r : P.Address} {nfw rootw : Nat}
    (hTransport : Call.inputs (.withdraw nf tok amt rcpt root) = ClientInputs E n r nfw rootw)
    {L : List Nat} {txs : List (Tx P)} {st : St P}
    (hrun : Run sup txs st) (hR : RepP H E sup L σ st)
    {G : List Nat} {Q : List (Nat × MPath)} (hPT : PathTreeHyp H G Q) (hLG : L <+: G)
    (hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆ Q)
    (hcr : CryptoHyp P (txs ++ [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])])) :
    tokenCalls tr = [.transfer (E.tok n.token) n.amount (E.addr r)] := by
  obtain ⟨d, -, -, -, -, -, -, htc, -⟩ :=
    withdraw_journey hWP hEnv hW hPF hinj hreach hpin hx hA2 hTransport hrun hR hPT hLG hQ hcr
  rw [htc]

end LeanShieldedPool.Refine.Journey
