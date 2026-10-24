//! Serde wrappers at ethsystems/pocs a04b8b38969dfc2ee64de47edee7e396454204a8,
//! root `pocs/private-payment/shielded-pool/src/lib/`:
//!   NoteDomain::encode_note            crypto/encryption.rs:45-47
//!   NoteDomain::decode_note            crypto/encryption.rs:49-51
//!   viewing_pubkey_serde::serialize    domain/keys.rs:116-122
//!   viewing_pubkey_serde::deserialize  domain/keys.rs:124-130
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. THIN WRAPPERS: serde, serde_json and k256 are abstract trait parameters.
//! The proofs show only what the wrapper adds: which library call gets which argument, the
//! compressed SEC1 flag, the append-to-`out` behaviour, and error propagation/mapping.
//! Nothing about the JSON codec, the serde data model or curve points is proved.
//!
//! Stand-ins (faithfulness READ, not proved):
//! - serde_json is a trait parameter `J: JsonApi` (`serde_json::to_writer` / `from_slice` become
//!   `J::to_writer` / `J::from_slice`); `impl Domain for NoteDomain` (external sealring trait)
//!   becomes inherent `NoteDomain::encode_note<J>` / `decode_note<J>`; `Self::Note` is `Note`,
//!   `Self::Error` is `J::Error`.
//! - `serialize` / `deserialize` stay in `mod viewing_pubkey_serde`; each gains `<.., P>`.
//! - serde's `Serializer` / `Deserializer<'de>` are local stand-in traits with abstract spec
//!   functions; `Deserialize::deserialize(deserializer)` for `Vec<u8>` becomes
//!   `D::deserialize_vec(deserializer)`; `serde::de::Error::custom` becomes `D::custom`.
//! - k256::PublicKey is a trait parameter `P: PublicKeyApi` (as in key_wrappers.rs);
//!   `k256::PublicKey::from_sec1_bytes` becomes `P::from_sec1_bytes`.
use vstd::prelude::*;

verus! {

pub struct Note {
    pub token: [u8; 20],
    pub amount_hi: u128,
    pub amount_lo: u128,
    pub owner_pubkey: [u8; 32],
    pub salt: [u8; 32],
}

pub trait JsonApi {
    type Error;
    spec fn encodes(note: Note) -> bool;
    spec fn json_of(note: Note) -> Seq<u8>;
    spec fn decoded(bytes: Seq<u8>) -> Result<Note, Self::Error>;
    fn to_writer(out: &mut Vec<u8>, note: &Note) -> (r: Result<(), Self::Error>)
        ensures
            (r is Ok) == Self::encodes(*note),
            r is Ok ==> final(out)@ == old(out)@ + Self::json_of(*note);
    fn from_slice(bytes: &[u8]) -> (r: Result<Note, Self::Error>)
        ensures r == Self::decoded(bytes@);
}

pub struct NoteDomain;

impl NoteDomain {
    pub fn encode_note<J: JsonApi>(note: &Note, out: &mut Vec<u8>) -> (r: Result<(), J::Error>)
        ensures
            (r is Ok) == J::encodes(*note),
            r is Ok ==> final(out)@ == old(out)@ + J::json_of(*note),
    {
        J::to_writer(out, note)
    }

    pub fn decode_note<J: JsonApi>(bytes: &[u8]) -> (r: Result<Note, J::Error>)
        ensures r == J::decoded(bytes@),
    {
        J::from_slice(bytes)
    }
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

pub trait Serializer: Sized {
    type Ok;
    type Error;
    spec fn ser_bytes(self, v: Seq<u8>) -> Result<Self::Ok, Self::Error>;
    fn serialize_bytes(self, v: &[u8]) -> (r: Result<Self::Ok, Self::Error>)
        ensures r == self.ser_bytes(v@);
}

pub trait Deserializer<E>: Sized {
    type Error;
    spec fn de_vec(self) -> Result<Seq<u8>, Self::Error>;
    spec fn custom_of(e: E) -> Self::Error;
    fn deserialize_vec(self) -> (r: Result<Vec<u8>, Self::Error>)
        ensures
            (r is Ok) == (self.de_vec() is Ok),
            r is Ok ==> r->Ok_0@ == self.de_vec()->Ok_0,
            r is Err ==> r == Err::<Vec<u8>, Self::Error>(self.de_vec()->Err_0);
    fn custom(e: E) -> (r: Self::Error)
        ensures r == Self::custom_of(e);
}

pub mod viewing_pubkey_serde {
    use super::*;

    pub fn serialize<S, P: PublicKeyApi>(key: &P, serializer: S) -> (r: Result<S::Ok, S::Error>)
        where
            S: Serializer,
        ensures r == serializer.ser_bytes(key.sec1(true)),
    {
        let bytes = key.to_sec1_point(true);
        serializer.serialize_bytes(bytes.as_bytes())
    }

    pub fn deserialize<D, P: PublicKeyApi>(deserializer: D) -> (r: Result<P, D::Error>)
        where
            D: Deserializer<P::Error>,
        ensures
            deserializer.de_vec() is Err ==> r == Err::<P, D::Error>(deserializer.de_vec()->Err_0),
            deserializer.de_vec() is Ok ==> ((r is Ok) == P::accepts_sec1(deserializer.de_vec()->Ok_0)),
            (deserializer.de_vec() is Ok && r is Ok) ==> r->Ok_0 == P::parsed_sec1(deserializer.de_vec()->Ok_0),
    {
        let bytes: Vec<u8> = D::deserialize_vec(deserializer)?;
        P::from_sec1_bytes(&bytes).map_err(D::custom)
    }
}

fn main() {
}

} // verus!
