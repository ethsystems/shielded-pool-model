//! The deposit and withdraw public-input serializers over the
//! FULL U256 amount domain, at ethsystems/pocs a04b8b38969dfc2ee64de47edee7e396454204a8,
//! `pocs/private-payment/shielded-pool/src/lib/domain/proof.rs`:
//!   DepositProof::public_inputs_as_array   lines 55-66   sha256 1947e68c...
//!   WithdrawProof::public_inputs_as_array  lines 182-190 sha256 e630a836...
//! A REVIEWED MIRROR, verified by Verus; NOT the shipped alloy code. Bodies are verbatim.
//!
//! Stand-ins:
//! - U256 is two u128 halves, value = hi * 2^128 + lo: all 2^256 values, no range premise.
//! - B256 is a newtype over [u8; 32] and Address a newtype over [u8; 20] (alloy FixedBytes).
//! - `From<U256> for B256` writes the 32 big-endian bytes (alloy src/bits/fixed.rs:119-126:
//!   `to_be_bytes`; read, not proved). `.into()` is the source text.
//! - `B256::left_padding_from` writes 32 - len zero bytes, then the slice (alloy
//!   src/bits/fixed.rs:563-569; read, not proved). `Address::as_slice` borrows the 20 bytes.
//! - The proof records keep only `public_inputs` (the `proof: Bytes` field is not read).
use vstd::prelude::*;

verus! {

pub struct U256 {
    pub lo: u128,
    pub hi: u128,
}

pub open spec fn p128() -> nat { 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat }

pub open spec fn value(x: U256) -> nat {
    x.hi as nat * p128() + x.lo as nat
}

impl Clone for U256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        U256 { lo: self.lo, hi: self.hi }
    }
}
impl Copy for U256 {}

pub struct B256(pub [u8; 32]);

impl Clone for B256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        B256(self.0)
    }
}
impl Copy for B256 {}

pub struct Address(pub [u8; 20]);

impl Clone for Address {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        Address(self.0)
    }
}
impl Copy for Address {}

impl Address {
    pub fn as_slice(&self) -> (r: &[u8])
        ensures r@ == self.0@,
    {
        self.0.as_slice()
    }
}

pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 256 * pow256((n - 1) as nat) }
}

/// Big-endian value of a byte sequence.
pub open spec fn be_value(w: Seq<u8>) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 } else { be_value(w.drop_last()) * 256 + w.last() as nat }
}

/// `w` is the 20 bytes of `a` behind 12 zero bytes.
pub open spec fn is_left_pad(w: Seq<u8>, a: Seq<u8>) -> bool {
    &&& w.len() == 32
    &&& a.len() == 20
    &&& forall|j: int| 0 <= j < 12 ==> w[j] == 0u8
    &&& forall|j: int| 0 <= j < 20 ==> w[12 + j] == a[j]
}

impl B256 {
    pub fn left_padding_from(value: &[u8]) -> (r: B256)
        requires value.len() <= 32,
        ensures
            forall|j: int| 0 <= j < 32 - value.len() ==> r.0@[j] == 0u8,
            forall|j: int| 0 <= j < value.len() ==> r.0@[32 - value.len() + j] == value@[j],
    {
        let mut out = [0u8; 32];
        let off = 32 - value.len();
        let mut i: usize = 0;
        while i < value.len()
            invariant
                off + value.len() == 32,
                i <= value.len(),
                out@.len() == 32,
                forall|j: int| 0 <= j < off ==> out@[j] == 0u8,
                forall|j: int| 0 <= j < i ==> out@[off + j] == value@[j],
            decreases value.len() - i,
        {
            out[off + i] = value[i];
            i += 1;
        }
        B256(out)
    }
}

/// One base-256 digit step, stated with shifts so no shift reaches 128 (as for the u128 words).
proof fn lemma_byte_step(x: u128, s: u32)
    requires s <= 112,
    ensures (x >> s) as nat == ((x >> (s + 8) as u32) as nat) * 256 + ((x >> s) & 0xff) as nat,
{
    let hi = x >> (s + 8) as u32;
    let lo = (x >> s) & 0xff;
    assert(x >> s == (hi << 8u32) | lo) by (bit_vector)
        requires s <= 112, hi == x >> (s + 8) as u32, lo == (x >> s) & 0xff;
    assert(hi <= 0x00ff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128) by (bit_vector)
        requires s <= 112, hi == x >> (s + 8) as u32;
    assert(lo <= 0xffu128) by (bit_vector)
        requires lo == (x >> s) & 0xff;
    assert((hi << 8u32) | lo == hi * 256 + lo) by (bit_vector)
        requires hi <= 0x00ff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128, lo <= 0xffu128;
}

proof fn lemma_top_byte(x: u128)
    ensures (x >> 120u32) as nat == ((x >> 120u32) & 0xff) as nat,
{
    assert(x >> 120u32 == (x >> 120u32) & 0xff) by (bit_vector);
}

/// 16 big-endian bytes of a u128.
pub fn be16(x: u128) -> (out: [u8; 16])
    ensures be_value(out@) == x as nat,
{
    let mut out = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            out@.len() == 16,
            0 < i ==> be_value(out@.subrange(0, i as int)) == (x >> (8 * (16 - i)) as u32) as nat,
        decreases 16 - i,
    {
        let shift = (8 * (15 - i)) as u32;
        let ghost old_out = out@;
        assert(((x >> shift) & 0xff) < 256) by (bit_vector);
        out[i] = ((x >> shift) & 0xff) as u8;
        proof {
            let s = out@.subrange(0, i as int + 1);
            assert(s.drop_last() =~= old_out.subrange(0, i as int));
            assert(s.last() == out@[i as int]);
            assert(be_value(s) == be_value(s.drop_last()) * 256 + s.last() as nat);
            if i == 0 {
                lemma_top_byte(x);
                assert(be_value(s.drop_last()) == 0);
                assert(shift == 120u32);
            } else {
                lemma_byte_step(x, shift);
                assert((8 * (16 - i)) as u32 == (shift + 8) as u32);
            }
        }
        i += 1;
    }
    assert(x >> 0u32 == x) by (bit_vector);
    assert(out@.subrange(0, 16) =~= out@);
    out
}

proof fn lemma_be_concat(a: Seq<u8>, b: Seq<u8>)
    ensures be_value(a + b) == be_value(a) * pow256(b.len()) + be_value(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(pow256(0) == 1);
        assert(be_value(b) == 0);
    } else {
        let b2 = b.drop_last();
        lemma_be_concat(a, b2);
        assert((a + b).drop_last() =~= a + b2);
        assert((a + b).last() == b.last());
        assert(be_value(a + b) == be_value((a + b).drop_last()) * 256 + (a + b).last() as nat);
        assert(be_value(b) == be_value(b2) * 256 + b.last() as nat);
        let x = be_value(a);
        let p = pow256(b2.len());
        assert(pow256(b.len()) == 256 * p);
        assert((x * p + be_value(b2)) * 256 + b.last() as nat == x * (256 * p) + (be_value(b2) * 256 + b.last() as nat))
            by (nonlinear_arith);
    }
}

/// `w` is the 32-byte big-endian word of `x`, for every x < 2^256.
pub open spec fn is_amount_word(w: Seq<u8>, x: U256) -> bool {
    &&& w.len() == 32
    &&& be_value(w) == value(x)
}

pub fn u256_to_be(x: U256) -> (out: [u8; 32])
    ensures is_amount_word(out@, x),
{
    let h = be16(x.hi);
    let l = be16(x.lo);
    let out = [h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8], h[9], h[10], h[11], h[12], h[13], h[14], h[15],
               l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], l[9], l[10], l[11], l[12], l[13], l[14], l[15]];
    proof {
        assert(out@ =~= h@ + l@);
        lemma_be_concat(h@, l@);
        assert(pow256(16) == p128()) by (compute);
    }
    out
}

impl vstd::std_specs::convert::FromSpecImpl<U256> for B256 {
    open spec fn obeys_from_spec() -> bool { false }
    open spec fn from_spec(v: U256) -> B256 { arbitrary() }
}

impl From<U256> for B256 {
    fn from(x: U256) -> (r: B256)
        ensures is_amount_word(r.0@, x),
    {
        B256(u256_to_be(x))
    }
}

pub struct DepositPublicInputs {
    pub commitment: B256,
    pub token: Address,
    pub amount: U256,
    pub funding_address: Address,
    pub attestation_root: B256,
    pub payload_hash: B256,
}

pub struct DepositProof {
    pub public_inputs: DepositPublicInputs,
}

pub struct WithdrawPublicInputs {
    pub nullifier: B256,
    pub token: Address,
    pub amount: U256,
    pub recipient: Address,
    pub commitment_root: B256,
}

pub struct WithdrawProof {
    pub public_inputs: WithdrawPublicInputs,
}

impl DepositProof {
    /// Get the public inputs as an array of B256 for contract verification.
    pub fn public_inputs_as_array(&self) -> (r: [B256; 6])
        ensures
            r[0] == self.public_inputs.commitment,
            is_left_pad(r[1].0@, self.public_inputs.token.0@),
            is_amount_word(r[2].0@, self.public_inputs.amount),
            is_left_pad(r[3].0@, self.public_inputs.funding_address.0@),
            r[4] == self.public_inputs.attestation_root,
            r[5] == self.public_inputs.payload_hash,
    {
        [
            self.public_inputs.commitment,
            B256::left_padding_from(self.public_inputs.token.as_slice()),
            self.public_inputs.amount.into(),
            B256::left_padding_from(self.public_inputs.funding_address.as_slice()),
            self.public_inputs.attestation_root,
            self.public_inputs.payload_hash,
        ]
    }
}

impl WithdrawProof {
    /// Get the public inputs as an array of B256 for contract verification.
    pub fn public_inputs_as_array(&self) -> (r: [B256; 5])
        ensures
            r[0] == self.public_inputs.nullifier,
            is_left_pad(r[1].0@, self.public_inputs.token.0@),
            is_amount_word(r[2].0@, self.public_inputs.amount),
            is_left_pad(r[3].0@, self.public_inputs.recipient.0@),
            r[4] == self.public_inputs.commitment_root,
    {
        [
            self.public_inputs.nullifier,
            B256::left_padding_from(self.public_inputs.token.as_slice()),
            self.public_inputs.amount.into(),
            B256::left_padding_from(self.public_inputs.recipient.as_slice()),
            self.public_inputs.commitment_root,
        ]
    }
}

/// With the PR #12 deposit guard's range (0 < amount < 2^128), the word is the old u128 word:
/// the top 16 bytes are zero. This links the full-domain result to the u128 mirrors.
pub proof fn guarded_amount_word_top_zero(w: Seq<u8>, x: U256)
    requires is_amount_word(w, x), value(x) < p128(),
    ensures x.hi == 0,
{
    assert(x.hi == 0) by (nonlinear_arith)
        requires (x.hi as nat * p128() + x.lo as nat) < p128();
}

fn main() {
}

} // verus!
