//! Hash-parameterised commitment, nullifier, key and witness construction at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, `pocs/private-payment/shielded-pool/src/lib/domain/`:
//!   Note::commitment                   note.rs:73-82
//!   Note::nullifier                    note.rs:86-88
//!   Commitment::nullifier              commitment.rs:41-44
//!   SpendingKey::derive_owner_pubkey   keys.rs:32-34
//!   DepositWitness::new                witness.rs:61-87
//!   TransferWitness::new               witness.rs:121-149
//!   WithdrawWitness::new               witness.rs:202-221
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus.
//!
//! "Hash-parameterised only": Poseidon and the keccak payload commitment are
//! a trait parameter `H: PoolHash` with abstract spec functions h1, h2, h4, pc. Nothing is
//! assumed about them: no collision resistance, no field reduction, no Poseidon correctness.
//! The claims are argument order, argument encoding, and field provenance.
//!
//! Stand-ins (the only differences from the source text):
//! - `poseidon1/2/4(..)` and `payload_commitment(..)` become `H::poseidon1/2/4(..)` and
//!   `H::payload_commitment(..)`; each function gains the type parameter `H`, and calls to
//!   `commitment()`, `nullifier(..)`, `derive_owner_pubkey()` pass it as `::<H>`.
//! - U256, B256, Address, `.into()`, `B256::left_padding_from`, `as_slice` as in
//!   public_inputs.rs (full U256 domain; alloy semantics read, not proved).
//! - The Merkle proof records keep their four fields; serde derives are dropped.
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

/// Big-endian value of a byte sequence (as in public_inputs.rs).
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


pub trait PoolHash {
    spec fn h1(a: B256) -> B256;
    spec fn h2(a: B256, b: B256) -> B256;
    spec fn h4(a: B256, b: B256, c: B256, d: B256) -> B256;
    spec fn pc(payload: Seq<u8>) -> B256;
    fn poseidon1(a: B256) -> (r: B256)
        ensures r == Self::h1(a);
    fn poseidon2(a: B256, b: B256) -> (r: B256)
        ensures r == Self::h2(a, b);
    fn poseidon4(a: B256, b: B256, c: B256, d: B256) -> (r: B256)
        ensures r == Self::h4(a, b, c, d);
    fn payload_commitment(payload: &[u8]) -> (r: B256)
        ensures r == Self::pc(payload@);
}

pub struct Commitment(pub B256);
pub struct Nullifier(pub B256);
pub struct OwnerPubkey(pub B256);

impl Clone for OwnerPubkey {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        OwnerPubkey(self.0)
    }
}
impl Copy for OwnerPubkey {}

pub struct SpendingKey(pub B256);

pub struct Note {
    pub token: Address,
    pub amount: U256,
    pub owner_pubkey: OwnerPubkey,
    pub salt: B256,
}

pub struct CommitmentMerkleProof {
    pub path: Vec<B256>,
    pub indices: Vec<u8>,
    pub leaf_index: u64,
    pub proof_length: usize,
}

pub struct AttestationMerkleProof {
    pub path: Vec<B256>,
    pub indices: Vec<u8>,
    pub leaf_index: u64,
    pub proof_length: usize,
}

/// c is H4(left-padded token, 32-byte big-endian amount, owner, salt), in that order.
pub open spec fn commitment_of<H: PoolHash>(n: Note, c: B256) -> bool {
    exists|t: B256, am: B256|
        #![trigger is_left_pad(t.0@, n.token.0@), is_amount_word(am.0@, n.amount)]
        is_left_pad(t.0@, n.token.0@) && is_amount_word(am.0@, n.amount)
            && c == H::h4(t, am, n.owner_pubkey.0, n.salt)
}

/// x is H2(commitment of n, spending key), in that order.
pub open spec fn nullifier_of<H: PoolHash>(n: Note, sk: SpendingKey, x: B256) -> bool {
    exists|c: B256| #![trigger commitment_of::<H>(n, c)] commitment_of::<H>(n, c) && x == H::h2(c, sk.0)
}

impl SpendingKey {
    /// Derive the owner public key (spending pubkey) from the spending key.
    /// owner_pubkey = poseidon1(spending_key)
    pub fn derive_owner_pubkey<H: PoolHash>(&self) -> (r: OwnerPubkey)
        ensures r.0 == H::h1(self.0),
    {
        OwnerPubkey(H::poseidon1(self.0))
    }
}

impl Commitment {
    /// Compute the nullifier for this commitment given the spending key.
    /// nullifier = poseidon2(commitment, spending_key)
    pub fn nullifier<H: PoolHash>(&self, spending_key: &SpendingKey) -> (r: Nullifier)
        ensures r.0 == H::h2(self.0, spending_key.0),
    {
        let hash = H::poseidon2(self.0, spending_key.0);
        Nullifier(hash)
    }
}

impl Note {
    /// Compute the commitment for this note.
    /// commitment = poseidon4(token, amount, owner_pubkey, salt)
    pub fn commitment<H: PoolHash>(&self) -> (r: Commitment)
        ensures commitment_of::<H>(*self, r.0),
    {
        // Convert address to B256 (pad with zeros on the left)
        let token_b256 = B256::left_padding_from(self.token.as_slice());

        // Convert amount to B256
        let amount_b256: B256 = self.amount.into();

        let hash = H::poseidon4(token_b256, amount_b256, self.owner_pubkey.0, self.salt);
        proof {
            assert(is_left_pad(token_b256.0@, self.token.0@));
            assert(is_amount_word(amount_b256.0@, self.amount));
        }
        Commitment(hash)
    }

    /// Compute the nullifier for this note given the spending key.
    /// nullifier = poseidon2(commitment, spending_key)
    pub fn nullifier<H: PoolHash>(&self, spending_key: &SpendingKey) -> (r: Nullifier)
        ensures nullifier_of::<H>(*self, *spending_key, r.0),
    {
        self.commitment::<H>().nullifier::<H>(spending_key)
    }
}

pub struct DepositWitness {
    pub commitment: B256,
    pub token: Address,
    pub amount: U256,
    pub funding_address: Address,
    pub attestation_root: B256,
    pub payload_hash: B256,
    pub spending_key: SpendingKey,
    pub owner_pubkey: OwnerPubkey,
    pub salt: B256,
    pub attester: Address,
    pub issued_at: u64,
    pub expires_at: u64,
    pub attestation_proof: AttestationMerkleProof,
}

impl DepositWitness {
    /// Create a deposit witness from a note, the depositor's spending key, the funding
    /// address, and attestation data.
    pub fn new<H: PoolHash>(
        note: &Note,
        spending_key: SpendingKey,
        funding_address: Address,
        attestation_root: B256,
        attester: Address,
        issued_at: u64,
        expires_at: u64,
        attestation_proof: AttestationMerkleProof,
        encrypted_payload: &[u8],
    ) -> (r: Self)
        ensures
            commitment_of::<H>(*note, r.commitment),
            r.token == note.token,
            r.amount == note.amount,
            r.funding_address == funding_address,
            r.attestation_root == attestation_root,
            r.payload_hash == H::pc(encrypted_payload@),
            r.owner_pubkey.0 == H::h1(spending_key.0),
            r.spending_key == spending_key,
            r.salt == note.salt,
            r.attester == attester,
            r.issued_at == issued_at,
            r.expires_at == expires_at,
            r.attestation_proof == attestation_proof,
    {
        Self {
            commitment: note.commitment::<H>().0,
            token: note.token,
            amount: note.amount,
            funding_address,
            attestation_root,
            payload_hash: H::payload_commitment(encrypted_payload),
            owner_pubkey: spending_key.derive_owner_pubkey::<H>(),
            spending_key,
            salt: note.salt,
            attester,
            issued_at,
            expires_at,
            attestation_proof,
        }
    }
}

pub struct TransferWitness {
    pub nullifiers: [B256; 2],
    pub output_commitments: [B256; 2],
    pub commitment_root: B256,
    pub payload_hash: B256,
    pub spending_key: SpendingKey,
    pub input_notes: [Note; 2],
    pub output_notes: [Note; 2],
    pub input_proofs: [CommitmentMerkleProof; 2],
}

impl TransferWitness {
    /// Create a transfer witness.
    pub fn new<H: PoolHash>(
        spending_key: SpendingKey,
        input_notes: [Note; 2],
        output_notes: [Note; 2],
        input_proofs: [CommitmentMerkleProof; 2],
        commitment_root: B256,
        encrypted_payload: &[u8],
    ) -> (r: Self)
        ensures
            nullifier_of::<H>(input_notes[0], spending_key, r.nullifiers[0]),
            nullifier_of::<H>(input_notes[1], spending_key, r.nullifiers[1]),
            commitment_of::<H>(output_notes[0], r.output_commitments[0]),
            commitment_of::<H>(output_notes[1], r.output_commitments[1]),
            r.commitment_root == commitment_root,
            r.payload_hash == H::pc(encrypted_payload@),
            r.spending_key == spending_key,
            r.input_notes == input_notes,
            r.output_notes == output_notes,
            r.input_proofs == input_proofs,
    {
        let nullifiers = [
            input_notes[0].nullifier::<H>(&spending_key).0,
            input_notes[1].nullifier::<H>(&spending_key).0,
        ];

        let output_commitments = [
            output_notes[0].commitment::<H>().0,
            output_notes[1].commitment::<H>().0,
        ];

        Self {
            nullifiers,
            output_commitments,
            commitment_root,
            payload_hash: H::payload_commitment(encrypted_payload),
            spending_key,
            input_notes,
            output_notes,
            input_proofs,
        }
    }
}

pub struct WithdrawWitness {
    pub nullifier: B256,
    pub token: Address,
    pub amount: U256,
    pub recipient: Address,
    pub commitment_root: B256,
    pub spending_key: SpendingKey,
    pub note: Note,
    pub commitment_proof: CommitmentMerkleProof,
}

impl WithdrawWitness {
    /// Create a withdraw witness.
    pub fn new<H: PoolHash>(
        spending_key: SpendingKey,
        note: Note,
        commitment_proof: CommitmentMerkleProof,
        commitment_root: B256,
        recipient: Address,
    ) -> (r: Self)
        ensures
            nullifier_of::<H>(note, spending_key, r.nullifier),
            r.token == note.token,
            r.amount == note.amount,
            r.recipient == recipient,
            r.commitment_root == commitment_root,
            r.spending_key == spending_key,
            r.note == note,
            r.commitment_proof == commitment_proof,
    {
        let nullifier = note.nullifier::<H>(&spending_key).0;

        Self {
            nullifier,
            token: note.token,
            amount: note.amount,
            recipient,
            commitment_root,
            spending_key,
            note,
            commitment_proof,
        }
    }
}

fn main() {
}

} // verus!
