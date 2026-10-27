//! Viewing-key wrappers, note encryption and receipt conversion at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, root `pocs/private-payment/shielded-pool/src/lib/`:
//!   ViewingKey::random                 domain/keys.rs:66-68
//!   ViewingKey::from_bytes             domain/keys.rs:71-73
//!   ViewingKey::derive_viewing_pubkey  domain/keys.rs:76-78
//!   ViewingPubkey::from_sec1_bytes     domain/keys.rs:92-94
//!   ViewingPubkey::to_sec1_bytes       domain/keys.rs:102-105
//!   encrypt_note                       crypto/encryption.rs:55-64
//!   EthereumRpc::convert_receipt       adapters/ethereum_rpc.rs:163-170
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. It is NOT the shipped k256 / sealring / alloy code. These are thin wrappers:
//! the proofs show only what the wrapper adds (argument passing, the compress flag, error
//! propagation, the empty AAD, byte copying, the unwrap_or default). Curve arithmetic, key
//! validity, sealing, entropy and receipts stay abstract.
//!
//! Stand-ins (faithfulness READ, not proved):
//! - k256::SecretKey and k256::PublicKey are trait parameters `S: SecretKeyApi` and
//!   `P: PublicKeyApi` (ViewingKey<S>, ViewingPubkey<P>); `k256::SecretKey::from_slice`,
//!   `generate_from_rng`, `public_key`, `k256::PublicKey::from_sec1_bytes`, `to_sec1_point`
//!   become `S::..` / `P::..` calls or trait-method calls with abstract spec functions. The only
//!   premise: each call is a function of its arguments.
//! - `rand::rng()` is dropped; the RNG is an input `rng: &mut Rng` holding the bytes it will
//!   supply (as note_key.rs does for Note::new). No claim about entropy or freshness.
//! - sealring 0.3.0 `seal` is a trait parameter `Z: SealApi<P>`. PREMISE (the source's own
//!   `expect` message, not proved): sealing to a valid public key returns Ok. sealring
//!   src/seal.rs:193-240 returns Err only for an all-zero shared secret, a note-encoding error,
//!   an AEAD error, or a parse failure of its own output (read).
//! - `AAD` (`const AAD: &[u8] = &[]`) becomes a local `[u8; 0]`: this Verus release rejects the
//!   slice constant (a probe run, not kept here). `.to_vec()` becomes `to_vec_u8(..)`.
//!   The `use k256::elliptic_curve::sec1::ToSec1Point;` line is dropped (trait import).
//! - alloy TransactionReceipt keeps the four fields read (alloy-rpc-types-eth 1.6.1
//!   src/transaction/receipt.rs:16-40); `status()` returns a stand-in `status_flag` (the
//!   real method reads the receipt envelope's status, receipt.rs:143-150: read).
use vstd::prelude::*;

verus! {

pub struct Rng {
    pub seed: Vec<u8>,
}

pub struct EncodedPoint {
    pub bytes: Vec<u8>,
}

impl EncodedPoint {
    pub fn as_bytes(&self) -> (r: &[u8])
        ensures r@ == self.bytes@,
    {
        self.bytes.as_slice()
    }
}

pub trait PublicKeyApi: Sized {
    type Error;
    spec fn accepts_sec1(bytes: Seq<u8>) -> bool;
    spec fn parsed_sec1(bytes: Seq<u8>) -> Self;
    spec fn sec1(&self, compress: bool) -> Seq<u8>;
    fn from_sec1_bytes(bytes: &[u8]) -> (r: Result<Self, Self::Error>)
        ensures
            (r is Ok) == Self::accepts_sec1(bytes@),
            r is Ok ==> r->Ok_0 == Self::parsed_sec1(bytes@);
    fn to_sec1_point(&self, compress: bool) -> (r: EncodedPoint)
        ensures r.bytes@ == self.sec1(compress);
}

pub trait SecretKeyApi: Sized {
    type Public: PublicKeyApi;
    type Error;
    spec fn accepts(bytes: Seq<u8>) -> bool;
    spec fn parsed(bytes: Seq<u8>) -> Self;
    spec fn pk(&self) -> Self::Public;
    spec fn generated(seed: Seq<u8>) -> Self;
    fn from_slice(bytes: &[u8]) -> (r: Result<Self, Self::Error>)
        ensures
            (r is Ok) == Self::accepts(bytes@),
            r is Ok ==> r->Ok_0 == Self::parsed(bytes@);
    fn public_key(&self) -> (r: Self::Public)
        ensures r == self.pk();
    fn generate_from_rng(rng: &mut Rng) -> (r: Self)
        ensures r == Self::generated(old(rng).seed@);
}

pub fn to_vec_u8(s: &[u8]) -> (r: Vec<u8>)
    ensures r@ == s@,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s.len(), out@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        out.push(s[i]);
        i += 1;
        assert(out@ =~= s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

pub struct ViewingKey<S: SecretKeyApi>(pub S);

impl<S: SecretKeyApi> ViewingKey<S> {
    /// Generate a random viewing key.
    pub fn random(rng: &mut Rng) -> (r: Self)
        ensures r.0 == S::generated(old(rng).seed@),
    {
        Self(S::generate_from_rng(rng))
    }

    /// Create from raw bytes.
    pub fn from_bytes(bytes: &[u8]) -> (r: Result<Self, S::Error>)
        ensures
            (r is Ok) == S::accepts(bytes@),
            r is Ok ==> r->Ok_0.0 == S::parsed(bytes@),
    {
        Ok(Self(S::from_slice(bytes)?))
    }

    /// Derive the viewing public key.
    pub fn derive_viewing_pubkey(&self) -> (r: ViewingPubkey<S::Public>)
        ensures r.0 == self.0.pk(),
    {
        ViewingPubkey(self.0.public_key())
    }
}

pub struct ViewingPubkey<P: PublicKeyApi>(pub P);

impl<P: PublicKeyApi> ViewingPubkey<P> {
    /// Create from raw compressed bytes (33 bytes).
    pub fn from_sec1_bytes(bytes: &[u8]) -> (r: Result<Self, P::Error>)
        ensures
            (r is Ok) == P::accepts_sec1(bytes@),
            r is Ok ==> r->Ok_0.0 == P::parsed_sec1(bytes@),
    {
        Ok(Self(P::from_sec1_bytes(bytes)?))
    }

    /// Get the public key reference.
    pub fn public_key(&self) -> (r: &P)
        ensures *r == self.0,
    {
        &self.0
    }

    /// Serialize to compressed SEC1 format (33 bytes).
    pub fn to_sec1_bytes(&self) -> (r: Vec<u8>)
        ensures r@ == self.0.sec1(true),
    {
        to_vec_u8(self.0.to_sec1_point(true).as_bytes())
    }
}

pub struct Note {
    pub token: [u8; 20],
    pub amount_hi: u128,
    pub amount_lo: u128,
    pub owner_pubkey: [u8; 32],
    pub salt: [u8; 32],
}

pub struct EncryptedNote {
    pub bytes: Vec<u8>,
}

impl EncryptedNote {
    pub fn new(bytes: Vec<u8>) -> (r: Self)
        ensures r.bytes == bytes,
    {
        Self { bytes }
    }
}

#[derive(Debug)]
pub struct SealError;

pub trait EnvelopeApi {
    spec fn bytes(&self) -> Seq<u8>;
    fn as_bytes(&self) -> (r: &[u8])
        ensures r@ == self.bytes();
}

pub trait SealApi<P> {
    type Envelope: EnvelopeApi;
    spec fn sealed(pk: P, note: Note, aad: Seq<u8>, seed: Seq<u8>) -> Self::Envelope;
    fn seal(pk: &P, note: &Note, aad: &[u8], rng: &mut Rng) -> (r: Result<Self::Envelope, SealError>)
        ensures
            r is Ok,
            r->Ok_0 == Self::sealed(*pk, *note, aad@, old(rng).seed@);
}

/// Encrypt a note for a recipient's viewing public key.
pub fn encrypt_note<P: PublicKeyApi, Z: SealApi<P>>(note: &Note, recipient: &ViewingPubkey<P>, rng: &mut Rng) -> (r: EncryptedNote)
    ensures r.bytes@ == Z::sealed(recipient.0, *note, Seq::<u8>::empty(), old(rng).seed@).bytes(),
{
    let aad: [u8; 0] = [];
    proof { assert(aad@ =~= Seq::<u8>::empty()); }
    let envelope = Z::seal(
        recipient.public_key(),
        note,
        &aad,
        rng,
    )
    .expect("sealing to a valid secp256k1 public key never fails");
    EncryptedNote::new(to_vec_u8(envelope.as_bytes()))
}

pub struct B256(pub [u8; 32]);

impl Clone for B256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        B256(self.0)
    }
}
impl Copy for B256 {}

pub struct TransactionReceipt {
    pub transaction_hash: B256,
    pub block_number: Option<u64>,
    pub gas_used: u64,
    pub status_flag: bool,
}

impl TransactionReceipt {
    pub fn status(&self) -> (r: bool)
        ensures r == self.status_flag,
    {
        self.status_flag
    }
}

pub struct TxReceipt {
    pub tx_hash: B256,
    pub block_number: u64,
    pub gas_used: u64,
    pub success: bool,
}

/// A missing block number (a receipt without a block) becomes block 0.
pub open spec fn block_or_zero(b: Option<u64>) -> u64 {
    match b {
        Some(n) => n,
        None => 0,
    }
}

pub struct EthereumRpc;

impl EthereumRpc {
    /// Helper to convert alloy transaction receipt to our TxReceipt type.
    fn convert_receipt(receipt: &TransactionReceipt) -> (r: TxReceipt)
        ensures
            r.tx_hash == receipt.transaction_hash,
            r.block_number == block_or_zero(receipt.block_number),
            r.gas_used == receipt.gas_used,
            r.success == receipt.status_flag,
    {
        TxReceipt {
            tx_hash: receipt.transaction_hash,
            block_number: receipt.block_number.unwrap_or(0),
            gas_used: receipt.gas_used,
            success: receipt.status(),
        }
    }
}

fn main() {
}

} // verus!
