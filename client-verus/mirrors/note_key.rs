//! Note and key construction at ethsystems/pocs a04b8b38969dfc2ee64de47edee7e396454204a8,
//! `pocs/private-payment/shielded-pool/src/lib/domain/`:
//!   Note::new            note.rs:38-49  sha256 2e08528e...
//!   Note::zero           note.rs:67-69  sha256 332a0f8a...
//!   Note::is_zero        note.rs:91-93  sha256 156814e2...
//!   SpendingKey::random  keys.rs:18-23  sha256 6cd2a6e7...
//! A REVIEWED MIRROR, verified by Verus; NOT the shipped rand/alloy code.
//!
//! Stand-ins (the only differences from the source text):
//! - `let mut rng = rand::rng();` is dropped; the random bytes are an explicit input `rng: &Rng`.
//!   `rng.fill(&mut x[5..])` becomes `rng.fill_from(&mut x, 5)`, a verified copy of the
//!   supplied bytes into x[5..32]. Nothing here is a claim about entropy or freshness.
//! - B256 is a newtype over [u8; 32] with From<[u8; 32]> (alloy FixedBytes<32>); Address is [u8; 20].
//!   The plain [u8; 32] alias failed: vstd gives the reflexive From no usable postcondition
//!   (a probe run, not kept in this package).
//! - U256 is two u128 halves (value = hi * 2^128 + lo), with `U256::ZERO` and `==`.
//! - Note::new and Note::zero take the extra `rng` parameter; SpendingKey::random takes `rng`.
//! Property proved: the salt and the key are below 2^216, hence below the BN254 scalar
//! modulus r: the source comment "keep within the field". So b256_to_fr does not reduce them.
use vstd::prelude::*;

verus! {

pub type Address = [u8; 20];

/// alloy's B256 is FixedBytes<32>, a newtype over [u8; 32] whose From<[u8; 32]> wraps the array.
pub struct B256(pub [u8; 32]);

impl vstd::std_specs::convert::FromSpecImpl<[u8; 32]> for B256 {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(v: [u8; 32]) -> B256 { B256(v) }
}

impl From<[u8; 32]> for B256 {
    fn from(v: [u8; 32]) -> (r: B256)
        ensures r == B256(v),
    {
        B256(v)
    }
}

pub struct U256 {
    pub lo: u128,
    pub hi: u128,
}

pub open spec fn p128() -> int { 0x1_0000_0000_0000_0000_0000_0000_0000_0000int }

pub open spec fn value(x: U256) -> int {
    x.hi as int * p128() + x.lo as int
}

impl Clone for U256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        U256 { lo: self.lo, hi: self.hi }
    }
}
impl Copy for U256 {}

impl U256 {
    pub const ZERO: U256 = U256 { lo: 0, hi: 0 };
    pub const MAX: U256 = U256 { lo: u128::MAX, hi: u128::MAX };
}

pub fn u256_eq(a: &U256, b: &U256) -> (r: bool)
    ensures r == (value(*a) == value(*b)),
{
    let r = a.lo == b.lo && a.hi == b.hi;
    proof {
        if value(*a) == value(*b) {
            assert(a.lo == b.lo && a.hi == b.hi) by (nonlinear_arith)
                requires
                    a.hi as int * p128() + a.lo as int == b.hi as int * p128() + b.lo as int,
                    0 <= a.lo < p128(), 0 <= b.lo < p128(),
                    0 <= a.hi, 0 <= b.hi;
        }
    }
    r
}

impl vstd::std_specs::cmp::PartialEqSpecImpl for U256 {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &U256) -> bool { value(*self) == value(*other) }
}

impl PartialEq for U256 {
    fn eq(&self, other: &U256) -> (r: bool)
        ensures r == (value(*self) == value(*other)),
    {
        u256_eq(self, other)
    }
}

/// BN254 scalar field modulus r.
pub open spec fn bn254_r() -> nat {
    21888242871839275222246405745257275088548364400416034343698204186575808495617nat
}

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

/// `w` has 5 zero bytes, then the 27 supplied random bytes, and so lies in the field.
pub open spec fn canonical_field_bytes(w: Seq<u8>, random: Seq<u8>) -> bool {
    &&& w.len() == 32
    &&& forall|j: int| 0 <= j < 5 ==> w[j] == 0u8
    &&& forall|j: int| 5 <= j < 32 ==> w[j] == random[j]
    &&& be_value(w) < pow256(27)
    &&& be_value(w) < bn254_r()
}

proof fn lemma_be_zeros(w: Seq<u8>)
    requires forall|j: int| 0 <= j < w.len() ==> w[j] == 0u8,
    ensures be_value(w) == 0,
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_be_zeros(w.drop_last());
    }
}

/// k leading zero bytes bound the big-endian value by 256^(len - k).
proof fn lemma_be_leading_zeros(w: Seq<u8>, k: nat)
    requires
        k <= w.len(),
        forall|j: int| 0 <= j < k ==> w[j] == 0u8,
    ensures be_value(w) < pow256((w.len() - k) as nat),
    decreases w.len(),
{
    if w.len() == k {
        lemma_be_zeros(w);
    } else {
        lemma_be_leading_zeros(w.drop_last(), k);
        let p = pow256((w.len() - 1 - k) as nat);
        assert(pow256((w.len() - k) as nat) == 256 * p);
        assert(be_value(w) == be_value(w.drop_last()) * 256 + w.last() as nat);
    }
}

proof fn lemma_field_bound(w: Seq<u8>)
    requires w.len() == 32, forall|j: int| 0 <= j < 5 ==> w[j] == 0u8,
    ensures be_value(w) < pow256(27), be_value(w) < bn254_r(),
{
    lemma_be_leading_zeros(w, 5);
    assert(pow256(27) < bn254_r()) by (compute);
}

/// Stand-in for the thread RNG: the random bytes are an explicit input.
pub struct Rng {
    pub bytes: [u8; 32],
}

impl Rng {
    /// Stand-in for `rng.fill(&mut dest[start..])`: writes the supplied bytes there.
    pub fn fill_from(&self, dest: &mut [u8; 32], start: usize)
        requires start <= 32,
        ensures
            forall|j: int| 0 <= j < start ==> final(dest)@[j] == old(dest)@[j],
            forall|j: int| start <= j < 32 ==> final(dest)@[j] == self.bytes@[j],
    {
        let mut i = start;
        while i < 32
            invariant
                start <= i <= 32,
                dest@.len() == 32,
                forall|j: int| 0 <= j < start ==> dest@[j] == old(dest)@[j],
                forall|j: int| start <= j < i ==> dest@[j] == self.bytes@[j],
            decreases 32 - i,
        {
            dest[i] = self.bytes[i];
            i += 1;
        }
    }
}

pub struct OwnerPubkey(pub B256);

pub struct SpendingKey(pub B256);

pub struct Note {
    pub token: Address,
    pub amount: U256,
    pub owner_pubkey: OwnerPubkey,
    pub salt: B256,
}

impl SpendingKey {
    /// Generate a random spending key.
    pub fn random(rng: &Rng) -> (r: Self)
        ensures canonical_field_bytes(r.0.0@, rng.bytes@),
    {
        let mut bytes = [0u8; 32];
        rng.fill_from(&mut bytes, 5);
        proof { lemma_field_bound(bytes@); }
        Self(B256::from(bytes))
    }
}

impl Note {
    /// Create a new note with a random salt.
    pub fn new(token: Address, amount: U256, owner_pubkey: OwnerPubkey, rng: &Rng) -> (r: Self)
        ensures
            r.token == token,
            r.amount == amount,
            r.owner_pubkey == owner_pubkey,
            canonical_field_bytes(r.salt.0@, rng.bytes@),
    {
        let mut salt_bytes = [0u8; 32];
        rng.fill_from(&mut salt_bytes, 5); // keep within the field
        proof { lemma_field_bound(salt_bytes@); }

        Self {
            token,
            amount,
            owner_pubkey,
            salt: B256::from(salt_bytes),
        }
    }

    /// Create a zero-value note (used for padding 2-in-2-out transfers).
    pub fn zero(token: Address, owner_pubkey: OwnerPubkey, rng: &Rng) -> (r: Self)
        ensures
            value(r.amount) == 0,
            r.token == token,
            r.owner_pubkey == owner_pubkey,
            canonical_field_bytes(r.salt.0@, rng.bytes@),
    {
        Self::new(token, U256::ZERO, owner_pubkey, rng)
    }

    /// Check if this is a zero-value note.
    pub fn is_zero(&self) -> (r: bool)
        ensures r == (value(self.amount) == 0),
    {
        self.amount == U256::ZERO
    }
}

fn main() {
}

} // verus!
