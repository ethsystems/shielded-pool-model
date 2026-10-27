//! Field conversion and Poseidon/keccak wrappers at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, root `pocs/private-payment/shielded-pool/src/lib/`:
//!   b256_to_fr                 crypto/poseidon.rs:13-15
//!   fr_to_b256                 crypto/poseidon.rs:18-22
//!   poseidon1                  crypto/poseidon.rs:26-34
//!   poseidon2                  crypto/poseidon.rs:40-48
//!   poseidon4                  crypto/poseidon.rs:54-62
//!   payload_commitment         domain/commitment.rs:51-54
//!   PoseidonHash::hash         adapters/merkle_tree.rs:36-49
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. It is NOT the shipped arkworks / light-poseidon / alloy code.
//!
//! Stand-ins (the only differences from the source text; faithfulness is READ, not proved):
//! - `Fr` (ark-bn254 0.4.0 Fp256, modulus r = 2188...5617, src/fields/fr.rs) is a struct over a
//!   U256 (two u128 halves); its field value is `value(repr) % r`, so every Fr value is a
//!   field element. `Fr::from_be_bytes_mod_order` (ark-ff 0.4.2 src/fields/prime.rs:63-100:
//!   big-endian bytes, reduced mod r) is a verified reader for 32-byte input followed by a
//!   verified reduction; it requires `bytes.len() == 32`, which every call site here meets.
//! - `into_bigint` returns the canonical representative (< r); `BigInt` (ark-ff BigInt<4>) is a
//!   U256; `to_bytes_be` (ark-ff src/biginteger/mod.rs:527-541: 4 LE limbs, LE bytes, reversed)
//!   is a verified 32-byte big-endian writer.
//! - B256 is a newtype over [u8; 32]; `from_slice` requires length 32 (alloy
//!   src/bits/fixed.rs:544-549 panics otherwise), so each call is proved not to panic.
//!   `as_ref` / `as_slice` borrow the 32 bytes.
//! - Poseidon (light-poseidon 0.2.0) is a trait parameter `P: PoseidonHasher`:
//!   `Poseidon::<Fr>` / `Poseidon::<Fq>` become `P`, and each function gains `<P: ...>`.
//!   Its contract, READ from light-poseidon 0.2.0: `new_circom(n)` is Ok for 1 <= n <= 12
//!   (lib.rs:505-525, parameters/bn254_x5.rs:36-43081: widths 2..13), and `hash` is Ok
//!   exactly when `inputs.len() == n` (lib.rs:377-384; no other Err return in lib.rs:377-417).
//!   The hash values are abstract functions h1, h2, h4 of the FIELD VALUES of the inputs.
//!   Nothing is assumed about them (no Poseidon correctness, no collision resistance).
//! - keccak256 is a trait parameter `K: Keccak` with abstract spec `k`.
//! - `impl LeanIMTHasher<32> for PoseidonHash { fn hash }` becomes an inherent
//!   `PoseidonHash::hash<P>`; it requires `input.len() == 64` (two 32-byte nodes; lean-imt
//!   0.1.1 hashes the concatenation of two nodes: read).
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

pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 256 * pow256((n - 1) as nat) }
}

/// Big-endian value of a byte sequence (as in public_inputs.rs).
pub open spec fn be_value(w: Seq<u8>) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 } else { be_value(w.drop_last()) * 256 + w.last() as nat }
}

/// One base-256 digit step, stated with shifts so no shift reaches 128 (as in public_inputs.rs).
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


pub proof fn lemma_pow_mono(i: nat, j: nat)
    requires i <= j,
    ensures pow256(i) <= pow256(j),
    decreases j,
{
    if i < j {
        lemma_pow_mono(i, (j - 1) as nat);
        assert(pow256(j) == 256 * pow256((j - 1) as nat));
    }
}

pub proof fn lemma_be_bound(s: Seq<u8>)
    ensures be_value(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_be_bound(s.drop_last());
        let x = be_value(s.drop_last());
        let p = pow256((s.len() - 1) as nat);
        assert(pow256(s.len()) == 256 * p);
        let l = s.last() as nat;
        assert(x * 256 + l < 256 * p) by (nonlinear_arith)
            requires x < p, l < 256;
    } else {
        assert(pow256(0) == 1);
    }
}

/// Big-endian u128 of the 16 bytes of `s` from `start`.
pub fn be_u128(s: &[u8], start: usize) -> (r: u128)
    requires start + 16 <= s.len(),
    ensures r as nat == be_value(s@.subrange(start as int, start + 16)),
{
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    assert(s@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    while i < 16
        invariant
            i <= 16,
            start + 16 <= s.len(),
            acc as nat == be_value(s@.subrange(start as int, start + i)),
        decreases 16 - i,
    {
        proof {
            lemma_be_bound(s@.subrange(start as int, start + i));
            lemma_pow_mono(i as nat, 15);
            assert(pow256(15) == 1329227995784915872903807060280344576nat) by (compute);
        }
        let ghost old_acc = acc;
        acc = acc * 256 + s[start + i] as u128;
        proof {
            let t = s@.subrange(start as int, start + i + 1);
            assert(t.drop_last() =~= s@.subrange(start as int, start + i));
            assert(t.last() == s@[start + i]);
        }
        i += 1;
    }
    acc
}

/// BN254 scalar field modulus r (ark-bn254 0.4.0 src/fields/fr.rs, read).
pub open spec fn R() -> nat { 21888242871839275222246405745257275088548364400416034343698204186575808495617nat }
pub const R_HI: u128 = 0x30644e72e131a029b85045b68181585d;
pub const R_LO: u128 = 0x2833e84879b9709143e1f593f0000001;

pub proof fn lemma_r_split()
    ensures R() == R_HI as nat * p128() + R_LO as nat, R_LO > 0,
{
    assert(21888242871839275222246405745257275088548364400416034343698204186575808495617nat
        == 0x30644e72e131a029b85045b68181585dnat * 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat
           + 0x2833e84879b9709143e1f593f0000001nat) by (compute);
}

pub fn ge_r(x: U256) -> (b: bool)
    ensures b == (value(x) >= R()),
{
    proof { lemma_r_split(); }
    x.hi > R_HI || (x.hi == R_HI && x.lo >= R_LO)
}

pub fn sub_r(x: U256) -> (y: U256)
    requires value(x) >= R(),
    ensures value(y) == value(x) - R(),
{
    proof { lemma_r_split(); }
    if x.lo >= R_LO {
        U256 { lo: x.lo - R_LO, hi: x.hi - R_HI }
    } else {
        U256 { lo: x.lo + (u128::MAX - R_LO + 1), hi: x.hi - R_HI - 1 }
    }
}

/// value(x) mod r by repeated subtraction (at most 5 rounds, since 2^256 < 6r).
pub fn reduce(x: U256) -> (y: U256)
    ensures value(y) == value(x) % R(), value(y) < R(),
{
    let mut y = x;
    let ghost mut k: nat = 0;
    while ge_r(y)
        invariant value(x) == k * R() + value(y),
        decreases value(y),
    {
        y = sub_r(y);
        proof { k = k + 1; }
    }
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            value(x) as int, R() as int, k as int, value(y) as int);
    }
    y
}

/// Stand-in for ark-ff BigInt<4>: the canonical 256-bit integer.
pub struct BigInt(pub U256);

impl BigInt {
    /// Stand-in for BigInteger::to_bytes_be: 32 big-endian bytes.
    pub fn to_bytes_be(&self) -> (r: Vec<u8>)
        ensures r@.len() == 32, be_value(r@) == value(self.0),
    {
        let w = u256_to_be(self.0);
        let mut out: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < 32
            invariant i <= 32, out@ == w@.subrange(0, i as int),
            decreases 32 - i,
        {
            out.push(w[i]);
            i += 1;
            assert(out@ =~= w@.subrange(0, i as int));
        }
        assert(w@.subrange(0, 32) =~= w@);
        out
    }
}

/// Stand-in for ark-bn254 Fr: any U256, read as its residue mod r.
pub struct Fr {
    pub repr: U256,
}

impl Clone for Fr {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        Fr { repr: self.repr }
    }
}
impl Copy for Fr {}

impl Fr {
    pub open spec fn val(&self) -> nat { value(self.repr) % R() }

    /// Stand-in for PrimeField::from_be_bytes_mod_order, for 32-byte input.
    pub fn from_be_bytes_mod_order(bytes: &[u8]) -> (r: Fr)
        requires bytes.len() == 32,
        ensures r.val() == be_value(bytes@) % R(), value(r.repr) < R(),
    {
        let hi = be_u128(bytes, 0);
        let lo = be_u128(bytes, 16);
        proof {
            lemma_be_concat(bytes@.subrange(0, 16), bytes@.subrange(16, 32));
            assert(bytes@.subrange(0, 16) + bytes@.subrange(16, 32) =~= bytes@);
            assert(pow256(16) == p128()) by (compute);
        }
        let y = reduce(U256 { lo, hi });
        proof { vstd::arithmetic::div_mod::lemma_small_mod(value(y), R()); }
        Fr { repr: y }
    }

    /// Stand-in for PrimeField::into_bigint: the canonical representative.
    pub fn into_bigint(&self) -> (r: BigInt)
        ensures value(r.0) == self.val(), value(r.0) < R(),
    {
        BigInt(reduce(self.repr))
    }
}

impl B256 {
    pub fn as_ref(&self) -> (r: &[u8])
        ensures r@ == self.0@,
    {
        self.0.as_slice()
    }

    pub fn as_slice(&self) -> (r: &[u8])
        ensures r@ == self.0@,
    {
        self.0.as_slice()
    }

    /// Stand-in for FixedBytes::from_slice: requires the length alloy requires (else panic).
    pub fn from_slice(src: &[u8]) -> (r: B256)
        requires src.len() == 32,
        ensures r.0@ == src@,
    {
        let mut out = [0u8; 32];
        let mut i: usize = 0;
        while i < 32
            invariant i <= 32, src.len() == 32, out@.len() == 32,
                forall|j: int| 0 <= j < i ==> out@[j] == src@[j],
            decreases 32 - i,
        {
            out[i] = src[i];
            i += 1;
        }
        assert(out@ =~= src@);
        B256(out)
    }
}

#[derive(Debug)]
pub enum PoseidonError {
    InvalidWidthCircom,
    InvalidNumberOfInputs,
}

/// light-poseidon 0.2.0 as a parameter; the contract is read (see the header).
pub trait PoseidonHasher: Sized {
    spec fn nr_inputs(&self) -> nat;
    spec fn h1(a: nat) -> nat;
    spec fn h2(a: nat, b: nat) -> nat;
    spec fn h4(a: nat, b: nat, c: nat, d: nat) -> nat;
    fn new_circom(nr_inputs: usize) -> (r: Result<Self, PoseidonError>)
        ensures 1 <= nr_inputs <= 12 ==> (r is Ok && r->Ok_0.nr_inputs() == nr_inputs);
    fn hash(&mut self, inputs: &[Fr]) -> (r: Result<Fr, PoseidonError>)
        ensures
            inputs.len() == old(self).nr_inputs() ==> r is Ok,
            (inputs.len() == old(self).nr_inputs() && inputs.len() == 1) ==>
                r->Ok_0.val() == Self::h1(inputs@[0].val()) % R(),
            (inputs.len() == old(self).nr_inputs() && inputs.len() == 2) ==>
                r->Ok_0.val() == Self::h2(inputs@[0].val(), inputs@[1].val()) % R(),
            (inputs.len() == old(self).nr_inputs() && inputs.len() == 4) ==>
                r->Ok_0.val() == Self::h4(inputs@[0].val(), inputs@[1].val(), inputs@[2].val(), inputs@[3].val()) % R();
}

/// keccak256 as a parameter.
pub trait Keccak {
    spec fn k(payload: Seq<u8>) -> B256;
    fn keccak256(payload: &[u8]) -> (r: B256)
        ensures r == Self::k(payload@);
}

/// Field value of a 32-byte word: big-endian, reduced mod r.
pub open spec fn fe(v: B256) -> nat { be_value(v.0@) % R() }

/// Convert B256 to BN254 field element.
fn b256_to_fr(value: B256) -> (r: Fr)
    ensures r.val() == fe(value),
{
    Fr::from_be_bytes_mod_order(value.as_ref())
}

/// Convert BN254 field element to B256.
fn fr_to_b256(value: Fr) -> (r: B256)
    ensures be_value(r.0@) == value.val(), be_value(r.0@) < R(),
{
    let big_int = value.into_bigint();
    let bytes = big_int.to_bytes_be();
    B256::from_slice(&bytes)
}

/// Poseidon hash with 1 input (for key derivation).
pub fn poseidon1<P: PoseidonHasher>(a: B256) -> (r: B256)
    ensures be_value(r.0@) == P::h1(fe(a)) % R(), be_value(r.0@) < R(),
{
    let mut hasher =
        P::new_circom(1).expect("Failed to create Poseidon hasher");
    let input = b256_to_fr(a);
    let result = hasher
        .hash(&[input])
        .expect("Failed to compute Poseidon hash");
    fr_to_b256(result)
}

/// Poseidon hash with 2 inputs (for nullifiers and Merkle nodes).
pub fn poseidon2<P: PoseidonHasher>(a: B256, b: B256) -> (r: B256)
    ensures be_value(r.0@) == P::h2(fe(a), fe(b)) % R(), be_value(r.0@) < R(),
{
    let mut hasher =
        P::new_circom(2).expect("Failed to create Poseidon hasher");
    let inputs = [b256_to_fr(a), b256_to_fr(b)];
    let result = hasher
        .hash(&inputs)
        .expect("Failed to compute Poseidon hash");
    fr_to_b256(result)
}

/// Poseidon hash with 4 inputs (for note commitments and attestation leaves).
pub fn poseidon4<P: PoseidonHasher>(a: B256, b: B256, c: B256, d: B256) -> (r: B256)
    ensures be_value(r.0@) == P::h4(fe(a), fe(b), fe(c), fe(d)) % R(), be_value(r.0@) < R(),
{
    let mut hasher =
        P::new_circom(4).expect("Failed to create Poseidon hasher");
    let inputs = [b256_to_fr(a), b256_to_fr(b), b256_to_fr(c), b256_to_fr(d)];
    let result = hasher
        .hash(&inputs)
        .expect("Failed to compute Poseidon hash");
    fr_to_b256(result)
}

/// Commitment to an encrypted payload: keccak256(payload) mod r, as 32 big-endian bytes.
pub fn payload_commitment<K: Keccak>(payload: &[u8]) -> (r: B256)
    ensures be_value(r.0@) == be_value(K::k(payload@).0@) % R(), be_value(r.0@) < R(),
{
    let reduced = Fr::from_be_bytes_mod_order(K::keccak256(payload).as_slice());
    B256::from_slice(&reduced.into_bigint().to_bytes_be())
}

/// Poseidon hasher for LeanIMT.
pub struct PoseidonHash;

impl PoseidonHash {
    pub fn hash<P: PoseidonHasher>(input: &[u8]) -> (r: [u8; 32])
        requires input.len() == 64,
        ensures
            be_value(r@) == P::h2(be_value(input@.subrange(0, 32)) % R(), be_value(input@.subrange(32, 64)) % R()) % R(),
            be_value(r@) < R(),
    {
        let hash = P::new_circom(2)
            .expect("Failed to initialize Poseidon")
            .hash(&[
                Fr::from_be_bytes_mod_order(&input[..32]),
                Fr::from_be_bytes_mod_order(&input[32..]),
            ])
            .expect("Poseidon hash failed");

        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash.into_bigint().to_bytes_be());

        hash_bytes
    }
}

fn main() {
}

} // verus!
