//! Verified conservation of the boost fee attribution step in `try_boosting`.
//!
//! Source: state-chain/pallets/cf-lending-pools/src/boost.rs
//!   - `fee_from_boosted_amount` (~453)
//!   - `boost_pool_fee = total_fee.saturating_sub(lending_pool_fee)` (~226)
//!   - reported `amounts` = principal + fee per source (~291-299)
//!
//! Verified:
//!   1. `fee_from_boosted_amount` ≡ nearest `Permill(5 bps) * deposit` and
//!      never exceeds the deposit.
//!   2. **Attribution conservation:** for any `lend_fee ≤ total_fee` and any
//!      split of `required = deposit - total_fee` into `(lend_p, boost_p)`,
//!      `(lend_p + lend_fee) + (boost_p + (total_fee - lend_fee)) = deposit`.
//!      The fee-attribution bookkeeping cannot create or destroy value.

use crate::network_fee::mul_ppm;
use vstd::prelude::*;

verus! {

pub const BOOST_FEE_BPS: u16 = 5;
pub const BPM: u32 = 100;

pub open spec fn boost_fee_of(deposit: int) -> int {
    crate::network_fee::ppm_of(deposit, (BOOST_FEE_BPS as int) * (BPM as int))
}

/// Port of `fee_from_boosted_amount` for the constant 5 bps boost fee.
pub fn fee_from_boosted_amount(deposit: u128) -> (r: u128)
    ensures
        r == boost_fee_of(deposit as int),
        r <= deposit,
{
    mul_ppm(deposit, (BOOST_FEE_BPS as u32) * BPM)
}

/// Pure conservation of the attribution step. Holds for *any* `lend_fee`
/// between 0 and `total_fee` — so it is independent of the exact
/// `Permill::from_rational` rounding used to compute the lending share.
pub proof fn theorem_attribution_conserves(
    deposit: int,
    total_fee: int,
    lend_p: int,
    boost_p: int,
    lend_fee: int,
)
    requires
        deposit >= 0,
        0 <= total_fee <= deposit,
        lend_p + boost_p == deposit - total_fee,
        0 <= lend_fee <= total_fee,
        lend_p >= 0,
        boost_p >= 0,
    ensures
        ({
            let boost_fee = total_fee - lend_fee;
            (lend_p + lend_fee) + (boost_p + boost_fee) == deposit
        }),
{
    assert((lend_p + lend_fee) + (boost_p + (total_fee - lend_fee))
        == lend_p + boost_p + total_fee) by (nonlinear_arith);
    assert(lend_p + boost_p + total_fee == deposit) by (nonlinear_arith)
        requires lend_p + boost_p == deposit - total_fee;
}

/// Executable sanity check composing the verified fee with the conservation
/// theorem for an arbitrary lending-principal share.
pub fn check_attribution(deposit: u128, lend_p: u128) -> (ok: bool)
    requires
        deposit >= 1,
    ensures
        ok == true,
{
    let total_fee = fee_from_boosted_amount(deposit);
    let required = deposit - total_fee;
    let lend_p2 = if lend_p > required { required } else { lend_p };
    let boost_p = required - lend_p2;
    // Worst-case lend_fee (= total_fee) and best-case (= 0) both conserve.
    proof {
        theorem_attribution_conserves(
            deposit as int,
            total_fee as int,
            lend_p2 as int,
            boost_p as int,
            0,
        );
        theorem_attribution_conserves(
            deposit as int,
            total_fee as int,
            lend_p2 as int,
            boost_p as int,
            total_fee as int,
        );
    }
    true
}

} // verus!
