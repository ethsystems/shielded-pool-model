//! Reviewed mirrors, not verification of the shipped Rust source.
//! Written against an earlier commit of the client; the mirrored regions are byte-identical at
//! ethsystems/pocs a04b8b3, and source/manifest.json pins their hashes.
//!
//! Divergences (all bridges to production remain review arguments):
//! - Serde derives and unrelated imports/methods are omitted.
//! - EncryptedNote::from_bytes replaces unsupported slice to_vec with the
//!   verified copy_range loop. Its branch and error string are unchanged.
//! - EncryptedTransferNotes::from_bytes replaces unsupported u32::from_be_bytes
//!   with read_be32. Guards, byte subslices, `?`, errors and record are verbatim.
//! - Its precondition usize::BITS == 64 covers 64-bit targets.
//!   The source expression 4 + a u32 length can overflow on 32-bit targets.
//! - EncryptedNote::to_bytes is verbatim. The transfer encoder replaces
//!   u32::to_be_bytes with write_be32. Clone, capacity, casts, and extensions
//!   are unchanged, including u32 truncation for oversized first payloads.
//! - U256 is two u128 halves; B256 is [u8;32]. The closure calls verified
//!   word_to_be instead of alloy/ruint Into. Its exact big-endian byte order
//!   matches the read alloy declaration (src/bits/fixed.rs:119-125).
//! - from_contract_elements retains into_iter/map/collect and the range loop.
//!   The closure has an explicit proof contract; `_` becomes `i` so the
//!   proof can refer to the loop index. Apart from the word conversion, the
//!   executable statements are unchanged.
//! - Specs, proof blocks, and loop invariants are added throughout.
//! - Vec allocation follows vstd semantics. OOM and physical limits are
//!   outside the claim. No cryptographic envelope validity is asserted.
use vstd::prelude::*;

verus! {

pub struct EncryptedNote { pub bytes: Vec<u8> }
pub struct EncryptedTransferNotes {
    pub note_1: EncryptedNote,
    pub note_2: EncryptedNote,
}

pub fn copy_range(bytes: &[u8], start: usize, end: usize) -> (r: Vec<u8>)
    requires start <= end <= bytes.len(),
    ensures r@ == bytes@.subrange(start as int, end as int),
{
    let mut out = Vec::new();
    let mut i = start;
    while i < end
        invariant start <= i <= end <= bytes.len(),
                  out@ == bytes@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(bytes[i]);
        i += 1;
        assert(out@ =~= bytes@.subrange(start as int, i as int));
    }
    out
}

pub open spec fn be32(s: Seq<u8>) -> int
    recommends s.len() >= 4,
{
    s[0] as int * 16777216 + s[1] as int * 65536 + s[2] as int * 256 + s[3] as int
}

pub fn read_be32(bytes: &[u8]) -> (r: u32)
    requires bytes.len() >= 4,
    ensures r as int == be32(bytes@),
{
    bytes[0] as u32 * 16777216 + bytes[1] as u32 * 65536
        + bytes[2] as u32 * 256 + bytes[3] as u32
}

pub open spec fn note_decoded(s: Seq<u8>, r: Result<EncryptedNote, &'static str>) -> bool {
    if s.len() == 0 { r == Err("Empty bytes") }
    else { match r { Ok(n) => n.bytes@ == s, Err(_) => false } }
}

impl EncryptedNote {
    pub fn from_bytes(bytes: &[u8]) -> (r: Result<Self, &'static str>)
        ensures note_decoded(bytes@, r),
    {
        if bytes.is_empty() {
            return Err("Empty bytes");
        }
        assert(bytes@.subrange(0, bytes.len() as int) =~= bytes@);
        Ok(Self { bytes: copy_range(bytes, 0, bytes.len()) })
    }

    pub fn to_bytes(&self) -> (r: Vec<u8>)
        ensures r@ == self.bytes@,
    {
        self.bytes.clone()
    }
}

pub open spec fn frame_valid(s: Seq<u8>) -> bool {
    s.len() >= 4 && 0 < be32(s) && 4 + be32(s) < s.len()
}

pub open spec fn transfer_decoded(s: Seq<u8>, r: Result<EncryptedTransferNotes, &'static str>) -> bool {
    if s.len() < 4 { r == Err("Invalid encrypted transfer notes format") }
    else if s.len() < 4 + be32(s) { r == Err("Invalid encrypted transfer notes format") }
    else if be32(s) == 0 || s.len() == 4 + be32(s) { r == Err("Empty bytes") }
    else { match r {
        Ok(n) => n.note_1.bytes@ == s.subrange(4, 4 + be32(s))
            && n.note_2.bytes@ == s.subrange(4 + be32(s), s.len() as int),
        Err(_) => false,
    } }
}

impl EncryptedTransferNotes {
    pub fn from_bytes(bytes: &[u8]) -> (r: Result<Self, &'static str>)
        requires usize::BITS == 64,
        ensures transfer_decoded(bytes@, r),
                r is Ok <==> frame_valid(bytes@),
    {
        if bytes.len() < 4 {
            return Err("Invalid encrypted transfer notes format");
        }
        let len_1 = read_be32(bytes) as usize;
        if bytes.len() < 4 + len_1 {
            return Err("Invalid encrypted transfer notes format");
        }
        let note_1 = EncryptedNote::from_bytes(&bytes[4..4 + len_1])?;
        let note_2 = EncryptedNote::from_bytes(&bytes[4 + len_1..])?;
        Ok(Self { note_1, note_2 })
    }
}

pub open spec fn header(n: u32) -> Seq<u8> {
    seq![(n >> 24) as u8, (n >> 16) as u8, (n >> 8) as u8, n as u8]
}

pub fn write_be32(n: u32) -> (r: [u8; 4])
    ensures r@ == header(n),
{
    let r = [(n >> 24) as u8, (n >> 16) as u8, (n >> 8) as u8, n as u8];
    assert(r@ =~= header(n));
    r
}

pub proof fn header_inverse(n: u32)
    ensures be32(header(n)) == n as int,
{
    assert(n == ((n >> 24) as u8 as u32) * 16777216
              + ((n >> 16) as u8 as u32) * 65536
              + ((n >> 8) as u8 as u32) * 256 + (n as u8 as u32)) by (bit_vector);
}

pub proof fn header_truncation(n: u64)
    ensures be32(header(n as u32)) == n as int % 4294967296,
{
    header_inverse(n as u32);
    assert((n as u32) as u64 == n % 4294967296u64) by (bit_vector);
}

pub open spec fn frame(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    header(a.len() as u32) + a + b
}

impl EncryptedTransferNotes {
    pub fn to_bytes(&self) -> (r: Vec<u8>)
        requires 4 + self.note_1.bytes.len() + self.note_2.bytes.len() <= usize::MAX,
        ensures r@ == frame(self.note_1.bytes@, self.note_2.bytes@),
                be32(r@) == self.note_1.bytes.len() as int % 4294967296,
    {
        let bytes_1 = self.note_1.to_bytes();
        let bytes_2 = self.note_2.to_bytes();
        let mut bytes = Vec::with_capacity(4 + bytes_1.len() + bytes_2.len());
        bytes.extend_from_slice(&write_be32(bytes_1.len() as u32));
        bytes.extend_from_slice(&bytes_1);
        bytes.extend_from_slice(&bytes_2);
        proof { header_truncation(bytes_1.len() as u64); }
        bytes
    }
}

pub fn note_roundtrip(note: &EncryptedNote) -> (r: EncryptedNote)
    requires note.bytes.len() > 0,
    ensures r.bytes@ == note.bytes@,
{
    let encoded = note.to_bytes();
    match EncryptedNote::from_bytes(encoded.as_slice()) {
        Ok(n) => n,
        Err(_) => { assert(false); unreachable!() },
    }
}

pub fn transfer_roundtrip(notes: &EncryptedTransferNotes) -> (r: EncryptedTransferNotes)
    requires usize::BITS == 64,
             0 < notes.note_1.bytes.len() <= u32::MAX,
             notes.note_2.bytes.len() > 0,
             4 + notes.note_1.bytes.len() + notes.note_2.bytes.len() <= usize::MAX,
    ensures r.note_1.bytes@ == notes.note_1.bytes@,
            r.note_2.bytes@ == notes.note_2.bytes@,
{
    let encoded = notes.to_bytes();
    proof {
        let a = notes.note_1.bytes@;
        let b = notes.note_2.bytes@;
        header_inverse(a.len() as u32);
        assert(be32(encoded@) == a.len());
        assert(encoded@.subrange(4, 4 + a.len() as int) =~= a);
        assert(encoded@.subrange(4 + a.len() as int, encoded.len() as int) =~= b);
    }
    match EncryptedTransferNotes::from_bytes(encoded.as_slice()) {
        Ok(n) => n,
        Err(_) => { assert(false); unreachable!() },
    }
}

pub struct U256 { pub lo: u128, pub hi: u128 }
pub type B256 = [u8; 32];

pub open spec fn word_byte(x: U256, j: int) -> u8
    recommends 0 <= j < 32,
{
    if j < 16 { (x.hi >> ((15 - j) * 8) as u32) as u8 }
    else { (x.lo >> ((31 - j) * 8) as u32) as u8 }
}

pub open spec fn word_bytes(x: U256) -> Seq<u8> {
    Seq::new(32, |j: int| word_byte(x, j))
}

pub fn word_to_be(x: &U256) -> (r: B256)
    ensures r@ == word_bytes(*x),
{
    let mut out = [0u8; 32];
    let mut j: usize = 0;
    while j < 32
        invariant j <= 32,
                  forall|k: int| #![trigger out@[k]] 0 <= k < j ==> out@[k] == word_byte(*x, k),
        decreases 32 - j,
    {
        if j < 16 {
            out[j] = (x.hi >> ((15 - j) * 8) as u32) as u8;
        } else {
            out[j] = (x.lo >> ((31 - j) * 8) as u32) as u8;
        }
        j += 1;
    }
    assert(out@ =~= word_bytes(*x));
    out
}

pub struct AttestationMerkleProof {
    pub path: Vec<B256>,
    pub indices: Vec<u8>,
    pub leaf_index: u64,
    pub proof_length: usize,
}

pub open spec fn suffix(leaf: u64, depth: int) -> u64 {
    if 0 <= depth < 64 { leaf >> (depth as u64) } else { 0 }
}

pub proof fn suffix_step(leaf: u64, depth: usize)
    ensures suffix(leaf, depth as int) >> 1u64 == suffix(leaf, depth as int + 1),
{
    if depth < 63 {
        let d = depth as u64;
        assert((leaf >> d) >> 1u64 == leaf >> (d + 1)) by (bit_vector)
            requires d < 63;
    } else if depth == 63 {
        assert((leaf >> 63u64) >> 1u64 == 0) by (bit_vector);
    } else {
        assert(0u64 >> 1u64 == 0) by (bit_vector);
    }
}

pub open spec fn contract_mapping(elements: Seq<U256>, leaf: u64, r: AttestationMerkleProof) -> bool {
    &&& r.path.len() == elements.len()
    &&& r.indices.len() == elements.len()
    &&& r.proof_length == elements.len()
    &&& r.leaf_index == leaf
    &&& forall|j: int| #![trigger r.path@[j]] 0 <= j < elements.len() ==>
            r.path@[j]@ == word_bytes(elements[j])
    &&& forall|j: int| #![trigger r.indices@[j]] 0 <= j < elements.len() ==>
            r.indices@[j] == (suffix(leaf, j) & 1u64) as u8
}

impl AttestationMerkleProof {
    pub fn from_contract_elements(elements: Vec<U256>, leaf_index: u64) -> (r: Self)
        ensures contract_mapping(elements@, leaf_index, r),
    {
        let path: Vec<B256> = elements.into_iter().map(|e: U256| -> (r: B256) ensures r@ == word_bytes(e) { word_to_be(&e) }).collect();
        let mut indices = Vec::with_capacity(path.len());
        let mut idx = leaf_index;
        assert(leaf_index >> 0u64 == leaf_index) by (bit_vector);
        assert(idx == suffix(leaf_index, 0));
        for i in 0..path.len()
            invariant i <= path.len(), indices.len() == i,
                      path.len() == elements.len(),
                      forall|k: int| #![trigger path@[k]] 0 <= k < path.len() ==>
                          path@[k]@ == word_bytes(elements@[k]),
                      forall|k: int| #![trigger indices@[k]] 0 <= k < i ==>
                          indices@[k] == (suffix(leaf_index, k) & 1u64) as u8,
                      idx == suffix(leaf_index, i as int),
        {
            indices.push((idx & 1) as u8);
            proof { suffix_step(leaf_index, i); }
            idx >>= 1;
        }
        let proof_length = path.len();
        Self { path, indices, leaf_index, proof_length }
    }
}

fn main() {}
}
