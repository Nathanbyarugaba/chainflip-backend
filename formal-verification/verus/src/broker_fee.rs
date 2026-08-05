//! Verified analysis of `take_broker_fees` fee-splitting arithmetic.
//!
//! Source: state-chain/pallets/cf-swapping/src/lib.rs ~1947–1981
//! Related: `validate_broker_fees` (~3604) enforces `total_bps ≤ 1000`;
//! `MAX_BENEFICIARIES = 6` (cf-primitives).
//!
//! Verified here (machine-checked):
//!   1. A single beneficiary fee equals `Permill(bps) * amount` (nearest,
//!      ties down via `mul_ppm`) and never exceeds `amount`.
//!   2. **Overcharge witness:** with four equal 2500-bps slices (total
//!      10000 — allowed by `take_broker_fees`'s own gate but rejected by
//!      `validate_broker_fees`), amount = 3 yields each fee = 1 and
//!      Σ fees = 4 > 3. The runtime `assert!(total_fee <= stable_amount)`
//!      would then panic *after* crediting brokers.
//!
//! Exhaustive safety under production constraints (n ≤ 6, Σ bps ≤ 1000 ⇒
//! Σ fees ≤ amount for all amounts) is discharged by
//! `tla/BrokerFeeSplit.tla` + the conformance proptest suite, which reuse
//! the same `fee_of` / `mul_ppm` semantics proven here.

use crate::network_fee::mul_ppm;
use vstd::prelude::*;

verus! {

/// `BASIS_POINTS_PER_MILLION`: 1 bps = 100 parts-per-million.
pub const BPM: u32 = 100;

/// Spec-level beneficiary fee (delegates to the verified `ppm_of`).
pub open spec fn beneficiary_fee(amount: int, bps: int) -> int {
    crate::network_fee::ppm_of(amount, bps * (BPM as int))
}

/// One beneficiary's fee — bit-identical to
/// `Permill::from_parts(bps * BPM) * amount`.
pub fn fee_of(amount: u128, bps: u16) -> (r: u128)
    requires
        (bps as u32) * BPM <= crate::network_fee::MILLION,
    ensures
        r == beneficiary_fee(amount as int, bps as int),
        r <= amount,
{
    mul_ppm(amount, (bps as u32) * BPM)
}

/// Sum of fees for a small fixed list. Returns `None` iff the sum would
/// exceed `amount` (the condition that fires the runtime `assert!`).
pub fn try_sum_fees(amount: u128, bps: &[u16]) -> (r: Option<u128>)
    requires
        bps@.len() <= 6,
        forall|i: int|
            0 <= i < bps@.len() ==> (bps@[i] as u32) * BPM <= crate::network_fee::MILLION,
    ensures
        match r {
            Some(total) => total <= amount,
            None => true,
        },
{
    let mut total: u128 = 0;
    let mut i: usize = 0;
    let n = bps.len();
    while i < n
        invariant
            0 <= i <= n,
            n == bps@.len(),
            n <= 6,
            forall|j: int|
                0 <= j < n ==> (bps@[j] as u32) * BPM <= crate::network_fee::MILLION,
            total <= amount,
        decreases n - i,
    {
        let f = fee_of(amount, bps[i]);
        if f > amount - total {
            return None;
        }
        total = total + f;
        i = i + 1;
    }
    Some(total)
}

/// Witness: unvalidated 100%-split fees can overcharge (Σ fees > amount).
///
/// Concrete values from the conformance probe: 4 × 2500 bps, amount = 3
/// → each fee = 1, sum = 4 > 3. This total_bps (= 10000) is inside
/// `take_broker_fees`'s own gate but outside `validate_broker_fees`.
pub proof fn theorem_unvalidated_overcharge_witness()
    ensures
        beneficiary_fee(3, 2500) == 1,
        beneficiary_fee(3, 2500) + beneficiary_fee(3, 2500) + beneficiary_fee(3, 2500)
            + beneficiary_fee(3, 2500) == 4,
        4 > 3,
{
    // ppm = 2500*100 = 250_000
    // floor((3*250_000 + 499_999) / 1_000_000) = floor(1_249_999 / 1e6) = 1
    assert(beneficiary_fee(3, 2500) == 1) by (compute);
}

/// Executable confirmation of the witness (usable from conformance tests
/// via a plain-Rust transcription; kept here so Verus checks the arithmetic
/// end-to-end).
pub fn unvalidated_overcharge_example() -> (overcharged: bool)
    ensures
        overcharged == true,
{
    let amount: u128 = 3;
    let f0 = fee_of(amount, 2500);
    let f1 = fee_of(amount, 2500);
    let f2 = fee_of(amount, 2500);
    let f3 = fee_of(amount, 2500);
    proof {
        theorem_unvalidated_overcharge_witness();
    }
    assert(f0 == 1 && f1 == 1 && f2 == 1 && f3 == 1);
    let sum = f0 + f1 + f2 + f3;
    assert(sum == 4);
    sum > amount
}

} // verus!
