//! Prover-input formatting and padding helpers at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, `pocs/private-payment/shielded-pool/src/lib/adapters/bb_prover.rs`:
//!   format_field               33-35
//!   format_field_from_address  38-41
//!   pad_field_array            49-53
//!   pad_index_array            56-60
//!   format_u256                44-46
//!   DepositProverInput::from   81-104
//!   TransferProverInput::from  139-175
//!   WithdrawProverInput::from  193-209
//!   BBProver::format_deposit_prover_toml   263-266
//!   BBProver::format_transfer_prover_toml  269-272
//!   BBProver::format_withdraw_prover_toml  275-278
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. It is NOT the shipped alloy formatting code.
//!
//! Stand-ins (faithfulness READ, not proved):
//! - `format!("{}", value)` for B256 becomes `fmt_display_b256(value)`, a verified writer of
//!   "0x" + 64 lowercase hex digits. alloy-primitives 1.5.4 src/bits/fixed.rs:220-225: Display
//!   without the alternate flag calls `fmt_hex::<false>(f, true)` (lines 673-678: lowercase
//!   hex of all bytes, with the "0x" prefix).
//! - `path.to_vec()` / `indices.to_vec()` become verified copies `to_vec_b256` / `to_vec_u8`
//!   (this Verus release gives slice `to_vec` no specification).
//! - The `map` closure gets an explicit contract; `Vec::resize`, `iter().map().collect()` are
//!   vstd's specifications.
//! - `value.to_string()` for U256 becomes `fmt_u256_decimal(value)`, a verified writer of the
//!   canonical decimal string (no sign, no leading zeros, "0" for zero) over the FULL U256
//!   domain. ruint 1.17.2 src/fmt.rs:49-84: Display prints u64/u128-sized values with the
//!   primitive Display and larger ones as big-endian base-10^19 spigots, the first unpadded
//!   and the rest zero-padded to 19 digits: the same canonical string (read).
//! - U256 is two u128 halves (uval = hi * 2^128 + lo), as in guards.rs; the spec function is
//!   named `uval` here because the source parameter of format_u256 is named `value`.
//! - The witness records (DepositWitness, TransferWitness, WithdrawWitness, Note, SpendingKey,
//!   OwnerPubkey, the Merkle proof records) keep exactly their fields; serde derives are
//!   dropped. The prover-input structs keep their fields and types; `#[derive(Serialize)]` is
//!   dropped (TOML output is out of scope). MAX_*_TREE_DEPTH are copied (domain/merkle.rs:12,16).
//! - `impl From<&XWitness> for XProverInput { fn from .. }` becomes an inherent
//!   `impl XProverInput { pub fn from .. }` (bodies verbatim; `XProverInput::from(w)` calls
//!   resolve the same way). Reason, machine-checked (probe runs, not kept here): with a
//!   `From<&T>` impl in the crate, this Verus release no longer proves `pad_field_array`'s
//!   `iter().map(..).collect()` postcondition (length and elements), with or without named
//!   lifetimes or a spun-off prover; without the impls it verifies.
//! - `toml::to_string` is a trait parameter `T: TomlApi` (`toml::to_string(&input)` becomes
//!   `T::to_string(&input)`; each format_*_prover_toml gains `<T>`; `BBProver` keeps no
//!   fields). The TOML TEXT is abstract (`T::text`): no faithful TOML stand-in exists here, so
//!   nothing about the text is proved. The contract states only when serialization fails, READ
//!   along the struct-field path toml 0.8.23 src/ser/map.rs:52-57 -> toml_edit 0.22.27
//!   src/ser/map.rs:196-202 and 446-447 -> src/ser/value.rs:108-113
//!   (versions pinned by the Cargo.lock at a04b8b3): a u64 (and so a usize) above i64::MAX is
//!   Err(out_of_range); strings, u8 arrays and string arrays always serialize (read).
//! - B256 and Address are newtypes over [u8; 32] and [u8; 20]; `B256::ZERO` is 32 zero bytes;
//!   `left_padding_from` and `as_slice` as in public_inputs.rs.
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


impl B256 {
    pub const ZERO: B256 = B256([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                                 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
}

pub open spec fn hex_char(n: nat) -> char {
    if n == 0 { '0' } else if n == 1 { '1' } else if n == 2 { '2' } else if n == 3 { '3' }
    else if n == 4 { '4' } else if n == 5 { '5' } else if n == 6 { '6' } else if n == 7 { '7' }
    else if n == 8 { '8' } else if n == 9 { '9' } else if n == 10 { 'a' } else if n == 11 { 'b' }
    else if n == 12 { 'c' } else if n == 13 { 'd' } else if n == 14 { 'e' } else { 'f' }
}

/// `s` is "0x" followed by two lowercase hex digits per byte of `b`, high nibble first.
pub open spec fn is_hex_of(s: Seq<char>, b: Seq<u8>) -> bool {
    &&& s.len() == 2 + 2 * b.len()
    &&& s[0] == '0'
    &&& s[1] == 'x'
    &&& forall|i: int| #![trigger b[i]] 0 <= i < b.len() ==>
            s[2 + 2 * i] == hex_char((b[i] / 16) as nat) && s[3 + 2 * i] == hex_char((b[i] % 16) as nat)
}

pub proof fn lemma_hex_char_injective(n: nat, m: nat)
    requires n < 16, m < 16, hex_char(n) == hex_char(m),
    ensures n == m,
{
}

/// The hex string determines the bytes: distinct words give distinct strings.
pub proof fn lemma_hex_injective(s: Seq<char>, b1: Seq<u8>, b2: Seq<u8>)
    requires is_hex_of(s, b1), is_hex_of(s, b2),
    ensures b1 == b2,
{
    assert(b1.len() == b2.len());
    assert forall|i: int| 0 <= i < b1.len() implies b1[i] == b2[i] by {
        let x = b1[i];
        let y = b2[i];
        assert(s[2 + 2 * i] == hex_char((x / 16) as nat));
        assert(s[2 + 2 * i] == hex_char((y / 16) as nat));
        lemma_hex_char_injective((x / 16) as nat, (y / 16) as nat);
        lemma_hex_char_injective((x % 16) as nat, (y % 16) as nat);
        assert(x == (x / 16) * 16 + x % 16);
        assert(y == (y / 16) * 16 + y % 16);
    }
    assert(b1 =~= b2);
}

fn hex_digit(n: u8) -> (c: char)
    requires n < 16,
    ensures c == hex_char(n as nat),
{
    if n == 0 { '0' } else if n == 1 { '1' } else if n == 2 { '2' } else if n == 3 { '3' }
    else if n == 4 { '4' } else if n == 5 { '5' } else if n == 6 { '6' } else if n == 7 { '7' }
    else if n == 8 { '8' } else if n == 9 { '9' } else if n == 10 { 'a' } else if n == 11 { 'b' }
    else if n == 12 { 'c' } else if n == 13 { 'd' } else if n == 14 { 'e' } else { 'f' }
}

/// Stand-in for `format!("{}", value)` on alloy B256 (full lowercase hex with 0x).
pub fn fmt_display_b256(value: &B256) -> (r: String)
    ensures is_hex_of(r@, value.0@),
{
    let mut s = String::new();
    s.push('0');
    s.push('x');
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            s@.len() == 2 + 2 * i,
            s@[0] == '0',
            s@[1] == 'x',
            forall|j: int| #![trigger value.0@[j]] 0 <= j < i ==>
                s@[2 + 2 * j] == hex_char((value.0@[j] / 16) as nat) && s@[3 + 2 * j] == hex_char((value.0@[j] % 16) as nat),
        decreases 32 - i,
    {
        let b = value.0[i];
        s.push(hex_digit(b / 16));
        s.push(hex_digit(b % 16));
        i += 1;
    }
    s
}

pub fn to_vec_b256(s: &[B256]) -> (r: Vec<B256>)
    ensures r@ == s@,
{
    let mut out: Vec<B256> = Vec::new();
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

/// 12 zero bytes, then the 20 address bytes.
pub open spec fn left_pad20(a: Seq<u8>) -> Seq<u8> {
    Seq::new(32, |j: int| if j < 12 { 0u8 } else { a[j - 12] })
}

pub open spec fn zero_word() -> Seq<u8> { Seq::new(32, |j: int| 0u8) }

/// Format a B256 as a hex string for Noir.
fn format_field(value: &B256) -> (r: String)
    ensures is_hex_of(r@, value.0@),
{
    fmt_display_b256(value)
}

/// Format an Address as a hex field for Noir (left-padded to 32 bytes).
fn format_field_from_address(addr: &Address) -> (r: String)
    ensures is_hex_of(r@, left_pad20(addr.0@)),
{
    let b256 = B256::left_padding_from(addr.as_slice());
    proof { assert(b256.0@ =~= left_pad20(addr.0@)); }
    format_field(&b256)
}

/// Pad a B256 path to `max_depth` and convert each element to a hex string.
/// The result has exactly max_depth entries: the path is zero-padded when shorter and
/// TRUNCATED when longer (Vec::resize).
fn pad_field_array(path: &[B256], max_depth: usize) -> (r: Vec<String>)
    ensures
        r.len() == max_depth,
        forall|i: int| 0 <= i < max_depth && i < path.len() ==> is_hex_of(#[trigger] r@[i]@, path@[i].0@),
        forall|i: int| 0 <= i < max_depth && i >= path.len() ==> is_hex_of(#[trigger] r@[i]@, zero_word()),
{
    let mut padded = to_vec_b256(path);
    padded.resize(max_depth, B256::ZERO);
    proof { assert(B256::ZERO.0@ =~= zero_word()); }
    padded.iter().map(|v: &B256| -> (r: String) ensures is_hex_of(r@, v.0@) { format_field(v) }).collect()
}

pub open spec fn padded_index(s: Seq<u8>, i: int) -> u8 {
    if i < s.len() { s[i] } else { 0u8 }
}

/// Pad an index array to `max_depth` (zero-padded when shorter, TRUNCATED when longer).
fn pad_index_array(indices: &[u8], max_depth: usize) -> (r: Vec<u8>)
    ensures
        r.len() == max_depth,
        forall|i: int| 0 <= i < max_depth ==> #[trigger] r@[i] == padded_index(indices@, i),
{
    let mut padded = to_vec_u8(indices);
    padded.resize(max_depth, 0);
    padded
}

pub struct U256 {
    pub lo: u128,
    pub hi: u128,
}

impl Clone for U256 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        U256 { lo: self.lo, hi: self.hi }
    }
}
impl Copy for U256 {}

pub open spec fn p128() -> nat { 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat }

pub open spec fn uval(x: U256) -> nat {
    x.hi as nat * p128() + x.lo as nat
}

pub open spec fn dec_char(d: nat) -> char {
    if d == 0 { '0' } else if d == 1 { '1' } else if d == 2 { '2' } else if d == 3 { '3' }
    else if d == 4 { '4' } else if d == 5 { '5' } else if d == 6 { '6' } else if d == 7 { '7' }
    else if d == 8 { '8' } else { '9' }
}

/// Canonical decimal string of n: no sign, no leading zeros, "0" for zero.
pub open spec fn dec_str(n: nat) -> Seq<char>
    decreases n,
{
    if n < 10 { seq![dec_char(n)] } else { dec_str(n / 10).push(dec_char(n % 10)) }
}

fn dec_digit(d: u8) -> (c: char)
    requires d < 10,
    ensures c == dec_char(d as nat),
{
    if d == 0 { '0' } else if d == 1 { '1' } else if d == 2 { '2' } else if d == 3 { '3' }
    else if d == 4 { '4' } else if d == 5 { '5' } else if d == 6 { '6' } else if d == 7 { '7' }
    else if d == 8 { '8' } else { '9' }
}

/// Full 256-bit division by 10, in 64-bit steps.
pub fn divmod10(x: U256) -> (res: (U256, u8))
    ensures uval(res.0) == uval(x) / 10, res.1 as nat == uval(x) % 10, res.1 < 10,
{
    let qh = x.hi / 10;
    let rh = x.hi % 10;
    let lo = x.lo;
    let l1 = lo >> 64u32;
    let l0 = lo & 0xffff_ffff_ffff_ffffu128;
    assert(lo == l1 * 0x1_0000_0000_0000_0000u128 + l0 && l1 < 0x1_0000_0000_0000_0000u128 && l0 < 0x1_0000_0000_0000_0000u128) by (bit_vector)
        requires l1 == lo >> 64u32, l0 == lo & 0xffff_ffff_ffff_ffffu128;
    let t1 = rh * 0x1_0000_0000_0000_0000u128 + l1;
    let q1 = t1 / 10;
    let r1 = t1 % 10;
    let t0 = r1 * 0x1_0000_0000_0000_0000u128 + l0;
    let q0 = t0 / 10;
    let r0 = t0 % 10;
    let ql = q1 * 0x1_0000_0000_0000_0000u128 + q0;
    let q = U256 { hi: qh, lo: ql };
    proof {
        let n = uval(x);
        assert(n == 10 * uval(q) + r0 as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n as int, 10, uval(q) as int, r0 as int);
    }
    (q, r0 as u8)
}

/// Digits `ds` (least significant first) as characters, most significant first.
pub open spec fn rev_chars(ds: Seq<u8>) -> Seq<char> {
    Seq::new(ds.len(), |i: int| dec_char(ds[ds.len() - 1 - i] as nat))
}

/// Stand-in for `value.to_string()` on ruint U256.
pub fn fmt_u256_decimal(x: &U256) -> (r: String)
    ensures r@ == dec_str(uval(*x)),
{
    let ghost n = uval(*x);
    let mut digits: Vec<u8> = Vec::new();
    let (q, d) = divmod10(*x);
    digits.push(d);
    let mut y = q;
    proof {
        assert(rev_chars(digits@) =~= seq![dec_char(d as nat)]);
        if n >= 10 {
            assert(dec_str(n) == dec_str(n / 10).push(dec_char(n % 10)));
            assert(dec_str(n) =~= dec_str(uval(y)) + rev_chars(digits@));
        }
    }
    while !(y.hi == 0 && y.lo == 0)
        invariant
            digits@.len() >= 1,
            forall|i: int| 0 <= i < digits@.len() ==> #[trigger] digits@[i] < 10,
            uval(y) > 0 ==> dec_str(n) == dec_str(uval(y)) + rev_chars(digits@),
            uval(y) == 0 ==> dec_str(n) == rev_chars(digits@),
        decreases uval(y),
    {
        let ghost old_digits = digits@;
        let ghost vy = uval(y);
        let (q, d) = divmod10(y);
        digits.push(d);
        y = q;
        proof {
            assert(vy > 0);
            assert(rev_chars(digits@) =~= seq![dec_char(d as nat)] + rev_chars(old_digits));
            if vy >= 10 {
                assert(dec_str(vy) == dec_str(vy / 10).push(dec_char(vy % 10)));
                assert(dec_str(vy) =~= dec_str(uval(y)) + seq![dec_char(d as nat)]);
                assert(dec_str(n) =~= dec_str(uval(y)) + rev_chars(digits@));
            } else {
                assert(uval(y) == 0);
                assert(dec_str(vy) =~= seq![dec_char(d as nat)]);
                assert(dec_str(n) =~= rev_chars(digits@));
            }
        }
    }
    let mut s = String::new();
    let mut i = digits.len();
    while i > 0
        invariant
            i <= digits@.len(),
            forall|k: int| 0 <= k < digits@.len() ==> #[trigger] digits@[k] < 10,
            s@ =~= rev_chars(digits@).subrange(0, (digits@.len() - i) as int),
        decreases i,
    {
        i -= 1;
        s.push(dec_digit(digits[i]));
        assert(s@ =~= rev_chars(digits@).subrange(0, (digits@.len() - i) as int));
    }
    assert(rev_chars(digits@).subrange(0, digits@.len() as int) =~= rev_chars(digits@));
    s
}

/// Format a U256 as a decimal string for Noir.
fn format_u256(value: &U256) -> (r: String)
    ensures r@ == dec_str(uval(*value)),
{
    fmt_u256_decimal(value)
}

pub const MAX_COMMITMENT_TREE_DEPTH: usize = 32;
pub const MAX_ATTESTATION_TREE_DEPTH: usize = 20;

pub struct SpendingKey(pub B256);
pub struct OwnerPubkey(pub B256);

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

/// `rs` is `path` padded (or truncated) to n entries, each formatted as a hex field.
pub open spec fn padded_path_ok(rs: Seq<String>, path: Seq<B256>, n: nat) -> bool {
    &&& rs.len() == n
    &&& forall|i: int| 0 <= i < n && i < path.len() ==> is_hex_of(#[trigger] rs[i]@, path[i].0@)
    &&& forall|i: int| 0 <= i < n && i >= path.len() ==> is_hex_of(#[trigger] rs[i]@, zero_word())
}

pub open spec fn padded_indices_ok(rs: Seq<u8>, ind: Seq<u8>, n: nat) -> bool {
    &&& rs.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] rs[i] == padded_index(ind, i)
}

pub struct DepositProverInput {
    pub commitment: String,
    pub token: String,
    pub amount: String,
    pub funding_address: String,
    pub attestation_root: String,
    pub payload_hash: String,
    pub spending_key: String,
    pub salt: String,
    pub attester: String,
    pub issued_at: u64,
    pub expires_at: u64,
    pub attestation_proof_length: usize,
    pub attestation_path: Vec<String>,
    pub attestation_indices: Vec<u8>,
}

pub open spec fn deposit_input_ok(r: DepositProverInput, w: DepositWitness) -> bool {
    &&& is_hex_of(r.commitment@, w.commitment.0@)
    &&& is_hex_of(r.token@, left_pad20(w.token.0@))
    &&& r.amount@ == dec_str(uval(w.amount))
    &&& is_hex_of(r.funding_address@, left_pad20(w.funding_address.0@))
    &&& is_hex_of(r.attestation_root@, w.attestation_root.0@)
    &&& is_hex_of(r.payload_hash@, w.payload_hash.0@)
    &&& is_hex_of(r.spending_key@, w.spending_key.0.0@)
    &&& is_hex_of(r.salt@, w.salt.0@)
    &&& is_hex_of(r.attester@, left_pad20(w.attester.0@))
    &&& r.issued_at == w.issued_at
    &&& r.expires_at == w.expires_at
    &&& r.attestation_proof_length == w.attestation_proof.proof_length
    &&& padded_path_ok(r.attestation_path@, w.attestation_proof.path@, 20)
    &&& padded_indices_ok(r.attestation_indices@, w.attestation_proof.indices@, 20)
}

impl DepositProverInput {
    pub fn from(w: &DepositWitness) -> (r: Self)
        ensures deposit_input_ok(r, *w),
    {
        Self {
            commitment: format_field(&w.commitment),
            token: format_field_from_address(&w.token),
            amount: format_u256(&w.amount),
            funding_address: format_field_from_address(&w.funding_address),
            attestation_root: format_field(&w.attestation_root),
            payload_hash: format_field(&w.payload_hash),
            spending_key: format_field(&w.spending_key.0),
            salt: format_field(&w.salt),
            attester: format_field_from_address(&w.attester),
            issued_at: w.issued_at,
            expires_at: w.expires_at,
            attestation_proof_length: w.attestation_proof.proof_length,
            attestation_path: pad_field_array(
                &w.attestation_proof.path,
                MAX_ATTESTATION_TREE_DEPTH,
            ),
            attestation_indices: pad_index_array(
                &w.attestation_proof.indices,
                MAX_ATTESTATION_TREE_DEPTH,
            ),
        }
    }
}

pub struct TransferProverInput {
    pub nullifier_0: String,
    pub nullifier_1: String,
    pub commitment_out_0: String,
    pub commitment_out_1: String,
    pub commitment_root: String,
    pub payload_hash: String,
    pub spending_key: String,
    pub token_in_0: String,
    pub amount_in_0: String,
    pub salt_in_0: String,
    pub token_in_1: String,
    pub amount_in_1: String,
    pub salt_in_1: String,
    pub token_out_0: String,
    pub amount_out_0: String,
    pub owner_out_0: String,
    pub salt_out_0: String,
    pub token_out_1: String,
    pub amount_out_1: String,
    pub owner_out_1: String,
    pub salt_out_1: String,
    pub proof_length_0: usize,
    pub path_0: Vec<String>,
    pub indices_0: Vec<u8>,
    pub proof_length_1: usize,
    pub path_1: Vec<String>,
    pub indices_1: Vec<u8>,
}

pub open spec fn transfer_input_ok(r: TransferProverInput, w: TransferWitness) -> bool {
    &&& is_hex_of(r.nullifier_0@, w.nullifiers[0].0@)
    &&& is_hex_of(r.nullifier_1@, w.nullifiers[1].0@)
    &&& is_hex_of(r.commitment_out_0@, w.output_commitments[0].0@)
    &&& is_hex_of(r.commitment_out_1@, w.output_commitments[1].0@)
    &&& is_hex_of(r.commitment_root@, w.commitment_root.0@)
    &&& is_hex_of(r.payload_hash@, w.payload_hash.0@)
    &&& is_hex_of(r.spending_key@, w.spending_key.0.0@)
    &&& is_hex_of(r.token_in_0@, left_pad20(w.input_notes[0].token.0@))
    &&& r.amount_in_0@ == dec_str(uval(w.input_notes[0].amount))
    &&& is_hex_of(r.salt_in_0@, w.input_notes[0].salt.0@)
    &&& is_hex_of(r.token_in_1@, left_pad20(w.input_notes[1].token.0@))
    &&& r.amount_in_1@ == dec_str(uval(w.input_notes[1].amount))
    &&& is_hex_of(r.salt_in_1@, w.input_notes[1].salt.0@)
    &&& is_hex_of(r.token_out_0@, left_pad20(w.output_notes[0].token.0@))
    &&& r.amount_out_0@ == dec_str(uval(w.output_notes[0].amount))
    &&& is_hex_of(r.owner_out_0@, w.output_notes[0].owner_pubkey.0.0@)
    &&& is_hex_of(r.salt_out_0@, w.output_notes[0].salt.0@)
    &&& is_hex_of(r.token_out_1@, left_pad20(w.output_notes[1].token.0@))
    &&& r.amount_out_1@ == dec_str(uval(w.output_notes[1].amount))
    &&& is_hex_of(r.owner_out_1@, w.output_notes[1].owner_pubkey.0.0@)
    &&& is_hex_of(r.salt_out_1@, w.output_notes[1].salt.0@)
    &&& r.proof_length_0 == w.input_proofs[0].proof_length
    &&& padded_path_ok(r.path_0@, w.input_proofs[0].path@, 32)
    &&& padded_indices_ok(r.indices_0@, w.input_proofs[0].indices@, 32)
    &&& r.proof_length_1 == w.input_proofs[1].proof_length
    &&& padded_path_ok(r.path_1@, w.input_proofs[1].path@, 32)
    &&& padded_indices_ok(r.indices_1@, w.input_proofs[1].indices@, 32)
}

impl TransferProverInput {
    pub fn from(w: &TransferWitness) -> (r: Self)
        ensures transfer_input_ok(r, *w),
    {
        Self {
            nullifier_0: format_field(&w.nullifiers[0]),
            nullifier_1: format_field(&w.nullifiers[1]),
            commitment_out_0: format_field(&w.output_commitments[0]),
            commitment_out_1: format_field(&w.output_commitments[1]),
            commitment_root: format_field(&w.commitment_root),
            payload_hash: format_field(&w.payload_hash),
            spending_key: format_field(&w.spending_key.0),
            token_in_0: format_field_from_address(&w.input_notes[0].token),
            amount_in_0: format_u256(&w.input_notes[0].amount),
            salt_in_0: format_field(&w.input_notes[0].salt),
            token_in_1: format_field_from_address(&w.input_notes[1].token),
            amount_in_1: format_u256(&w.input_notes[1].amount),
            salt_in_1: format_field(&w.input_notes[1].salt),
            token_out_0: format_field_from_address(&w.output_notes[0].token),
            amount_out_0: format_u256(&w.output_notes[0].amount),
            owner_out_0: format_field(&w.output_notes[0].owner_pubkey.0),
            salt_out_0: format_field(&w.output_notes[0].salt),
            token_out_1: format_field_from_address(&w.output_notes[1].token),
            amount_out_1: format_u256(&w.output_notes[1].amount),
            owner_out_1: format_field(&w.output_notes[1].owner_pubkey.0),
            salt_out_1: format_field(&w.output_notes[1].salt),
            proof_length_0: w.input_proofs[0].proof_length,
            path_0: pad_field_array(&w.input_proofs[0].path, MAX_COMMITMENT_TREE_DEPTH),
            indices_0: pad_index_array(
                &w.input_proofs[0].indices,
                MAX_COMMITMENT_TREE_DEPTH,
            ),
            proof_length_1: w.input_proofs[1].proof_length,
            path_1: pad_field_array(&w.input_proofs[1].path, MAX_COMMITMENT_TREE_DEPTH),
            indices_1: pad_index_array(
                &w.input_proofs[1].indices,
                MAX_COMMITMENT_TREE_DEPTH,
            ),
        }
    }
}

pub struct WithdrawProverInput {
    pub nullifier: String,
    pub token: String,
    pub amount: String,
    pub recipient: String,
    pub commitment_root: String,
    pub spending_key: String,
    pub salt: String,
    pub proof_length: usize,
    pub path: Vec<String>,
    pub indices: Vec<u8>,
}

pub open spec fn withdraw_input_ok(r: WithdrawProverInput, w: WithdrawWitness) -> bool {
    &&& is_hex_of(r.nullifier@, w.nullifier.0@)
    &&& is_hex_of(r.token@, left_pad20(w.token.0@))
    &&& r.amount@ == dec_str(uval(w.amount))
    &&& is_hex_of(r.recipient@, left_pad20(w.recipient.0@))
    &&& is_hex_of(r.commitment_root@, w.commitment_root.0@)
    &&& is_hex_of(r.spending_key@, w.spending_key.0.0@)
    &&& is_hex_of(r.salt@, w.note.salt.0@)
    &&& r.proof_length == w.commitment_proof.proof_length
    &&& padded_path_ok(r.path@, w.commitment_proof.path@, 32)
    &&& padded_indices_ok(r.indices@, w.commitment_proof.indices@, 32)
}

impl WithdrawProverInput {
    pub fn from(w: &WithdrawWitness) -> (r: Self)
        ensures withdraw_input_ok(r, *w),
    {
        Self {
            nullifier: format_field(&w.nullifier),
            token: format_field_from_address(&w.token),
            amount: format_u256(&w.amount),
            recipient: format_field_from_address(&w.recipient),
            commitment_root: format_field(&w.commitment_root),
            spending_key: format_field(&w.spending_key.0),
            salt: format_field(&w.note.salt),
            proof_length: w.commitment_proof.proof_length,
            path: pad_field_array(&w.commitment_proof.path, MAX_COMMITMENT_TREE_DEPTH),
            indices: pad_index_array(
                &w.commitment_proof.indices,
                MAX_COMMITMENT_TREE_DEPTH,
            ),
        }
    }
}

/// The formatted amount is the full decimal value: an amount of 2^128 or more is sent to the
/// prover as its own (long) decimal string, with no client range check in this path.
pub proof fn amount_string_unbounded()
    ensures dec_str(p128()).len() > 38,
{
    reveal_with_fuel(dec_str, 40);
    assert(dec_str(p128()).len() == 39) by (compute);
}

pub open spec fn i64_max() -> nat { 0x7fff_ffff_ffff_ffffnat }

/// Serialize-able prover inputs: when toml accepts every integer field.
pub trait TomlValue {
    spec fn ints_fit_i64(&self) -> bool;
}

impl TomlValue for DepositProverInput {
    open spec fn ints_fit_i64(&self) -> bool {
        self.issued_at <= i64_max() && self.expires_at <= i64_max() && self.attestation_proof_length <= i64_max()
    }
}

impl TomlValue for TransferProverInput {
    open spec fn ints_fit_i64(&self) -> bool {
        self.proof_length_0 <= i64_max() && self.proof_length_1 <= i64_max()
    }
}

impl TomlValue for WithdrawProverInput {
    open spec fn ints_fit_i64(&self) -> bool {
        self.proof_length <= i64_max()
    }
}

#[derive(Debug)]
pub struct TomlError;

/// toml 0.8.23 `to_string` as a parameter (see the header).
pub trait TomlApi {
    spec fn text<V: TomlValue>(v: V) -> Seq<char>;
    fn to_string<V: TomlValue>(value: &V) -> (r: Result<String, TomlError>)
        ensures
            (r is Ok) == value.ints_fit_i64(),
            r is Ok ==> r->Ok_0@ == Self::text(*value);
}

pub struct BBProver;

impl BBProver {
    /// Generate Prover.toml content for the deposit circuit. Does not panic exactly when the
    /// attestation timestamps and proof length fit i64 (under the read toml contract).
    fn format_deposit_prover_toml<T: TomlApi>(witness: &DepositWitness) -> (r: String)
        requires
            witness.issued_at <= i64_max(),
            witness.expires_at <= i64_max(),
            witness.attestation_proof.proof_length <= i64_max(),
        ensures exists|i: DepositProverInput| deposit_input_ok(i, *witness) && r@ == T::text(i),
    {
        let input = DepositProverInput::from(witness);
        T::to_string(&input).expect("failed to serialize deposit prover input")
    }

    /// Generate Prover.toml content for the transfer circuit.
    fn format_transfer_prover_toml<T: TomlApi>(witness: &TransferWitness) -> (r: String)
        requires
            witness.input_proofs[0].proof_length <= i64_max(),
            witness.input_proofs[1].proof_length <= i64_max(),
        ensures exists|i: TransferProverInput| transfer_input_ok(i, *witness) && r@ == T::text(i),
    {
        let input = TransferProverInput::from(witness);
        T::to_string(&input).expect("failed to serialize transfer prover input")
    }

    /// Generate Prover.toml content for the withdraw circuit.
    fn format_withdraw_prover_toml<T: TomlApi>(witness: &WithdrawWitness) -> (r: String)
        requires
            witness.commitment_proof.proof_length <= i64_max(),
        ensures exists|i: WithdrawProverInput| withdraw_input_ok(i, *witness) && r@ == T::text(i),
    {
        let input = WithdrawProverInput::from(witness);
        T::to_string(&input).expect("failed to serialize withdraw prover input")
    }
}

fn main() {
}

} // verus!
