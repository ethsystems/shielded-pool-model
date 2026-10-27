-- Control (must fail to compile): `Journey.withdraw_composed` with the per-path premise
-- `PathTreeHyp` dropped. The tree hop needs it to exclude the bad event `LeanImt.Bad` on the
-- note's retained path (a planted bad path folds a non-member to the root:
-- `PathToy.control_planted_bad`), so the composed conclusion does not follow. Every other premise
-- is supplied; the one goal left open is `PathTreeHyp H G Q`.
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
    {L : List Nat} {txs : List (Tx P)} {st : St P}
    (hrun : Run sup txs st) (hR : RepP H E sup L σ st)
    {G : List Nat} {Q : List (Nat × MPath)} (hLG : L <+: G)
    (hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆ Q)
    (hcr : CryptoHyp P (txs ++ [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])])) :
    ∃ d : WithdrawData P,
      d = { ext.withdraw [nf, tok, amt, rcpt, root] with snapshot := st.minted.length } ∧
      tok = E.tok d.note.token ∧ amt = d.note.amount ∧ rcpt = E.addr d.recipient ∧
      nf = E.nf d.nf ∧
      (∃ k ≤ L.length, root = rootOf H (L.take k) ∧ st.inTreeAt k d.note.cm) ∧
      d.guard st ∧
      Step st (.withdraw d) (d.post st) ∧
      RepP H E sup L σ' (d.post st) ∧
      tokenCalls tr = [.transfer (E.tok d.note.token) (E.addr d.recipient) d.note.amount] ∧
      (d.post st).withdrawn d.note.token = st.withdrawn d.note.token + d.note.amount ∧
      Run sup (txs ++ [.withdraw d]) (d.post st) ∧
      Money (txs ++ [.withdraw d]) (d.post st) := by
  refine withdraw_composed hWP hEnv hW hPF hinj hreach hpin hx hA2 hrun hR ?_ hLG hQ hcr

end LeanShieldedPool.Refine.Journey
