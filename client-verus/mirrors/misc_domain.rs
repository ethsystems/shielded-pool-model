//! Small domain and adapter functions at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, root `pocs/private-payment/shielded-pool/src/lib/`:
//!   P2pMessage::new       domain/encrypted.rs:62-72
//!   decrypt_note          crypto/encryption.rs:72-83
//!   b256_to_bytes         adapters/merkle_tree.rs:187-189
//!   bytes_to_b256         adapters/merkle_tree.rs:192-194
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. It is NOT the shipped sealring / k256 / alloy code.
//!
//! Stand-ins (faithfulness READ, not proved):
//! - sealring 0.3.0 is a trait parameter `S: Sealring`: `SealedNote::<K256, _>::parse` becomes
//!   `S::parse`, `Recipient::<K256>::new` becomes `S::recipient_new`, and
//!   `sealring::open::<K256, NoteDomain, _>` becomes `S::open`; `decrypt_note` gains `<S>`.
//!   The only premise: each call is a function of its arguments (abstract spec functions
//!   parses / envelope_of / recipient_of / opened). No property of the envelope, the KDF, the
//!   AEAD or the note codec is assumed.
//! - The closure `|_| ..` becomes `|_e: S::ParseError| -> (r: ..) ensures .. { .. }`: this
//!   Verus release accepts only variables as closure parameters, and needs the contract.
//! - `From<OpenError> for DecryptionError` is copied verbatim (it is the Aeneas-covered
//!   function, used here by `map_err`); its FromSpecImpl states the same mapping.
//! - k256::SecretKey and k256::PublicKey are opaque byte structs; Note is a plain record;
//!   EncryptedNote keeps its `bytes: Vec<u8>`; Commitment and B256 are newtypes.
//! - `alloy::primitives::B256::from_slice` becomes the stand-in `B256::from_slice`, which
//!   requires length 32 (alloy panics otherwise), so the call is proved not to panic.
use vstd::prelude::*;

verus! {

pub struct B256(pub [u8; 32]);

impl Clone for B256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        B256(self.0)
    }
}
impl Copy for B256 {}

impl B256 {
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

pub struct Commitment(pub B256);

pub struct PublicKey {
    pub sec1: [u8; 33],
}

pub struct ViewingPubkey(pub PublicKey);

pub struct SecretKey {
    pub scalar: [u8; 32],
}

impl Clone for SecretKey {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        SecretKey { scalar: self.scalar }
    }
}

pub struct ViewingKey(pub SecretKey);

impl ViewingKey {
    /// Get the secret key reference.
    pub fn secret_key(&self) -> (r: &SecretKey)
        ensures *r == self.0,
    {
        &self.0
    }
}

pub struct EncryptedNote {
    pub bytes: Vec<u8>,
}

impl EncryptedNote {
    pub fn as_bytes(&self) -> (r: &[u8])
        ensures r@ == self.bytes@,
    {
        self.bytes.as_slice()
    }
}

pub struct Note {
    pub token: [u8; 20],
    pub amount_hi: u128,
    pub amount_lo: u128,
    pub owner_pubkey: [u8; 32],
    pub salt: [u8; 32],
}

/// A P2P message containing an encrypted note and its commitment.
pub struct P2pMessage {
    pub encrypted_note: EncryptedNote,
    pub commitment: Commitment,
    pub recipient_viewing_pubkey: ViewingPubkey,
}

impl P2pMessage {
    /// Create a new P2P message.
    pub fn new(
        encrypted_note: EncryptedNote,
        commitment: Commitment,
        recipient_viewing_pubkey: ViewingPubkey,
    ) -> (r: Self)
        ensures
            r.encrypted_note == encrypted_note,
            r.commitment == commitment,
            r.recipient_viewing_pubkey == recipient_viewing_pubkey,
    {
        Self {
            encrypted_note,
            commitment,
            recipient_viewing_pubkey,
        }
    }
}

#[derive(Debug)]
pub enum OpenError {
    Aead,
    Verify,
    NoteDecode,
}

#[derive(Debug)]
pub enum DecryptionError {
    MalformedEnvelope,
    DecryptionFailed,
    DeserializationFailed,
}

pub open spec fn open_error_map(err: OpenError) -> DecryptionError {
    match err {
        OpenError::Aead => DecryptionError::DecryptionFailed,
        OpenError::Verify => DecryptionError::DecryptionFailed,
        OpenError::NoteDecode => DecryptionError::DeserializationFailed,
    }
}

impl vstd::std_specs::convert::FromSpecImpl<OpenError> for DecryptionError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(v: OpenError) -> DecryptionError { open_error_map(v) }
}

impl From<OpenError> for DecryptionError {
    fn from(err: OpenError) -> (r: Self)
        ensures r == open_error_map(err),
    {
        match err {
            OpenError::Aead | OpenError::Verify => Self::DecryptionFailed,
            OpenError::NoteDecode => Self::DeserializationFailed,
        }
    }
}

/// sealring 0.3.0 as a parameter (see the header).
pub trait Sealring {
    type Envelope;
    type Recipient;
    type ParseError;
    spec fn parses(bytes: Seq<u8>) -> bool;
    spec fn envelope_of(bytes: Seq<u8>) -> Self::Envelope;
    spec fn recipient_of(sk: SecretKey) -> Self::Recipient;
    spec fn opened(recipient: Self::Recipient, envelope: Self::Envelope, aad: Seq<u8>) -> Result<Option<Note>, OpenError>;
    fn parse(bytes: &[u8]) -> (r: Result<Self::Envelope, Self::ParseError>)
        ensures
            (r is Ok) == Self::parses(bytes@),
            r is Ok ==> r->Ok_0 == Self::envelope_of(bytes@);
    fn recipient_new(sk: SecretKey) -> (r: Self::Recipient)
        ensures r == Self::recipient_of(sk);
    fn open(recipient: &Self::Recipient, envelope: &Self::Envelope, aad: &[u8]) -> (r: Result<Option<Note>, OpenError>)
        ensures r == Self::opened(*recipient, *envelope, aad@);
}

/// The source's result, case by case: Ok only when the envelope parses and `open` returns
/// Some; a failed parse is MalformedEnvelope; Ok(None) (addressed elsewhere) is
/// DecryptionFailed; open errors map through From<OpenError>. AAD is empty.
pub open spec fn decrypt_spec<S: Sealring>(bytes: Seq<u8>, sk: SecretKey) -> Result<Note, DecryptionError> {
    if !S::parses(bytes) {
        Err(DecryptionError::MalformedEnvelope)
    } else {
        match S::opened(S::recipient_of(sk), S::envelope_of(bytes), Seq::<u8>::empty()) {
            Err(e) => Err(open_error_map(e)),
            Ok(None) => Err(DecryptionError::DecryptionFailed),
            Ok(Some(n)) => Ok(n),
        }
    }
}

/// Decrypt a note using the recipient's viewing key.
pub fn decrypt_note<S: Sealring>(
    encrypted: &EncryptedNote,
    viewing_key: &ViewingKey,
) -> (r: Result<Note, DecryptionError>)
    ensures r == decrypt_spec::<S>(encrypted.bytes@, viewing_key.0),
{
    let aad: [u8; 0] = [];
    let envelope = S::parse(encrypted.as_bytes())
        .map_err(|_e: S::ParseError| -> (r: DecryptionError) ensures r == DecryptionError::MalformedEnvelope { DecryptionError::MalformedEnvelope })?;
    let recipient = S::recipient_new(viewing_key.secret_key().clone());

    proof { assert(aad@ =~= Seq::<u8>::empty()); }
    S::open(&recipient, &envelope, &aad)
        .map_err(DecryptionError::from)?
        .ok_or(DecryptionError::DecryptionFailed)
}

/// Convert a B256 value to bytes for insertion into the tree.
pub fn b256_to_bytes(value: &B256) -> (r: [u8; 32])
    ensures r@ == value.0@,
{
    value.0
}

/// Convert bytes from the tree to a B256 value.
pub fn bytes_to_b256(bytes: &[u8; 32]) -> (r: B256)
    ensures r.0@ == bytes@,
{
    B256::from_slice(bytes)
}

fn main() {
}

} // verus!
