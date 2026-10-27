//! The client amount guards (ethsystems/pocs PR #12) and the token guard, at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, `pocs/private-payment/shielded-pool/src/lib/domain/witness.rs`:
//!   DepositWitness::validate_amount            lines 90-92   sha256 c244a2b2...
//!   TransferWitness::validate_amounts (+ sum)  lines 155-165 sha256 889d6346...
//!   TransferWitness::validate_token_consistency lines 168-173 sha256 6e0b65bf...
//! A REVIEWED MIRROR, verified by Verus; NOT the shipped alloy/ruint code.
//!
//! Stand-ins (the only differences from the source text):
//! - U256 is two u128 halves, value = hi * 2^128 + lo (the encoding of the Aeneas shim).
//!   `U256::ZERO`, `!=`/`==` and `TryFrom<U256> for u128` are implemented on it below.
//!   `u128::try_from` follows ruint 1.17.2 src/from.rs:751-765: Ok(low 128 bits) when the value
//!   is at most u128::MAX, else Err(Overflow(BITS, low bits, u128::MAX)). Read, not proved.
//! - `x == token` on `[u8; 20]` is `address_eq(&x, &token)`, a verified 20-byte loop
//!   (this Verus release gives array `==` no usable postcondition).
//! - Note, DepositWitness and TransferWitness keep only the fields the guards read.
use vstd::prelude::*;

verus! {

pub type Address = [u8; 20];

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

pub enum FromUintError {
    Overflow(usize, u128, u128),
}

pub open spec fn u128_try_from_spec(value: U256) -> Result<u128, FromUintError> {
    if value.hi == 0 { Ok(value.lo) } else { Err(FromUintError::Overflow(256, value.lo, u128::MAX)) }
}

impl vstd::std_specs::convert::TryFromSpecImpl<U256> for u128 {
    open spec fn obeys_try_from_spec() -> bool { true }
    open spec fn try_from_spec(value: U256) -> Result<u128, FromUintError> { u128_try_from_spec(value) }
}

impl core::convert::TryFrom<U256> for u128 {
    type Error = FromUintError;
    fn try_from(value: U256) -> (r: Result<u128, FromUintError>)
        ensures r == u128_try_from_spec(value),
    {
        if value.hi == 0 {
            Ok(value.lo)
        } else {
            Err(FromUintError::Overflow(256, value.lo, u128::MAX))
        }
    }
}

pub struct Note {
    pub token: Address,
    pub amount: U256,
}

pub struct DepositWitness {
    pub amount: U256,
}

pub struct TransferWitness {
    pub input_notes: [Note; 2],
    pub output_notes: [Note; 2],
}

/// The circuit's amount domain: 0 < amount < 2^128 for a deposit.
pub open spec fn deposit_amount_ok(w: &DepositWitness) -> bool {
    0 < value(w.amount) < p128()
}

pub open spec fn sum_spec(notes: &[Note; 2]) -> Option<u128> {
    let a = value(notes[0].amount);
    let b = value(notes[1].amount);
    if a < p128() && b < p128() && a + b < p128() { Some((a + b) as u128) } else { None }
}

pub open spec fn in_sum(w: &TransferWitness) -> int {
    value(w.input_notes[0].amount) + value(w.input_notes[1].amount)
}
pub open spec fn out_sum(w: &TransferWitness) -> int {
    value(w.output_notes[0].amount) + value(w.output_notes[1].amount)
}

/// Every amount and both sums fit u128 (the circuit's range and checked sums), and the
/// natural-number sums are equal. Stated over the full U256 source domain.
pub open spec fn transfer_amounts_ok(w: &TransferWitness) -> bool {
    &&& value(w.input_notes[0].amount) < p128()
    &&& value(w.input_notes[1].amount) < p128()
    &&& value(w.output_notes[0].amount) < p128()
    &&& value(w.output_notes[1].amount) < p128()
    &&& in_sum(w) < p128()
    &&& out_sum(w) < p128()
    &&& in_sum(w) == out_sum(w)
}

pub open spec fn same_tokens(w: &TransferWitness) -> bool {
    let t = w.input_notes[0].token@;
    &&& w.input_notes[1].token@ == t
    &&& w.output_notes[0].token@ == t
    &&& w.output_notes[1].token@ == t
}

pub fn address_eq(a: &Address, b: &Address) -> (r: bool)
    ensures r == (a@ == b@),
{
    let mut i: usize = 0;
    while i < 20
        invariant
            i <= 20,
            a@.len() == 20,
            b@.len() == 20,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases 20 - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

impl DepositWitness {
    /// Validate that the amount is non-zero and fits the circuit's `u128` amount.
    pub fn validate_amount(&self) -> (r: bool)
        ensures r == deposit_amount_ok(self),
    {
        self.amount != U256::ZERO && u128::try_from(self.amount).is_ok()
    }
}

impl TransferWitness {
    /// Validate that input amounts equal output amounts (value preservation).
    ///
    /// Mirrors the transfer circuit: every amount and both sums must fit in `u128`.
    /// `U256` addition wraps silently, so the sums are checked explicitly.
    pub fn validate_amounts(&self) -> (r: bool)
        ensures r == transfer_amounts_ok(self),
    {
        fn sum(notes: &[Note; 2]) -> (r: Option<u128>)
            ensures r == sum_spec(notes),
        {
            let a = u128::try_from(notes[0].amount).ok()?;
            let b = u128::try_from(notes[1].amount).ok()?;
            a.checked_add(b)
        }
        match (sum(&self.input_notes), sum(&self.output_notes)) {
            (Some(input_sum), Some(output_sum)) => input_sum == output_sum,
            _ => false,
        }
    }

    /// Validate that all notes use the same token.
    pub fn validate_token_consistency(&self) -> (r: bool)
        ensures r == same_tokens(self),
    {
        let token = self.input_notes[0].token;
        address_eq(&self.input_notes[1].token, &token)
            && address_eq(&self.output_notes[0].token, &token)
            && address_eq(&self.output_notes[1].token, &token)
    }
}

/// The source's own rows, witness.rs:305-317 (test_transfer_witness_amount_bounds),
/// plus a wrap witness (2^256-1 + 1 against 0 + 0), as closed examples over the mirror.
pub fn amount_bound_examples() {
    let max256 = U256 { lo: u128::MAX, hi: u128::MAX };
    let max = U256 { lo: u128::MAX, hi: 0 };
    let one = U256 { lo: 1, hi: 0 };
    let zero = U256::ZERO;
    let t = [7u8; 20];
    // U256::MAX + 1 wraps to 0 under U256 addition: now rejected.
    let w1 = TransferWitness {
        input_notes: [Note { token: t, amount: max256 }, Note { token: t, amount: one }],
        output_notes: [Note { token: t, amount: zero }, Note { token: t, amount: zero }],
    };
    // Sums equal in U256, overflowing the circuit's u128 addition: rejected.
    let w2 = TransferWitness {
        input_notes: [Note { token: t, amount: max }, Note { token: t, amount: one }],
        output_notes: [Note { token: t, amount: max }, Note { token: t, amount: one }],
    };
    // In range and conserved: accepted.
    let w3 = TransferWitness {
        input_notes: [Note { token: t, amount: max }, Note { token: t, amount: zero }],
        output_notes: [Note { token: t, amount: zero }, Note { token: t, amount: max }],
    };
    let r1 = w1.validate_amounts();
    let r2 = w2.validate_amounts();
    let r3 = w3.validate_amounts();
    assert(!r1);
    assert(!r2);
    assert(r3);
    // witness.rs:337-340 (test_deposit_witness_amount_bounds)
    let d0 = DepositWitness { amount: zero };
    let d1 = DepositWitness { amount: one };
    let d2 = DepositWitness { amount: max };
    let d3 = DepositWitness { amount: U256 { lo: 0, hi: 1 } };
    let a0 = d0.validate_amount();
    let a1 = d1.validate_amount();
    let a2 = d2.validate_amount();
    let a3 = d3.validate_amount();
    assert(!a0);
    assert(a1);
    assert(a2);
    assert(!a3);
}

/// What an accepted guard gives the rest of the pipeline, over the full U256 domain.
pub proof fn accepted_transfer_conserves(w: &TransferWitness)
    requires transfer_amounts_ok(w),
    ensures
        in_sum(w) == out_sum(w),
        value(w.input_notes[0].amount) < p128(),
        value(w.input_notes[1].amount) < p128(),
        value(w.output_notes[0].amount) < p128(),
        value(w.output_notes[1].amount) < p128(),
{
}

pub proof fn accepted_deposit_in_u128(w: &DepositWitness)
    requires deposit_amount_ok(w),
    ensures w.amount.hi == 0, w.amount.lo == value(w.amount), w.amount.lo > 0,
{
    assert(w.amount.hi == 0) by (nonlinear_arith)
        requires (w.amount.hi as int * p128() + w.amount.lo as int) < p128(), 0 <= w.amount.lo, 0 <= w.amount.hi;
}

fn main() {
}

} // verus!
