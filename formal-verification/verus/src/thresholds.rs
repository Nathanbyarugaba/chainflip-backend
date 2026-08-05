//! Verified threshold helpers (elections) and AMM fee-reduction specs.
//!
//! Sources:
//!   utilities/src/lib.rs — threshold_from_share_count / success_threshold_*
//!   state-chain/amm/src/lib.rs — reduce_by_pool_fee formula (~545)

use vstd::prelude::*;

verus! {

pub open spec fn threshold_from_share_count(n: int) -> int {
    if n <= 0 {
        0
    } else {
        (2 * n - 1) / 3
    }
}

pub open spec fn success_threshold_from_share_count(n: int) -> int {
    threshold_from_share_count(n) + 1
}

pub open spec fn failure_threshold_from_share_count(n: int) -> int {
    n - threshold_from_share_count(n)
}

pub fn threshold_from_share_count_exec(share_count: u32) -> (t: u32)
    requires
        share_count <= 0x7FFF_FFFF,  // 2*n fits in u32
    ensures
        t == threshold_from_share_count(share_count as int),
{
    if share_count == 0 {
        0
    } else {
        ((share_count * 2) - 1) / 3
    }
}

pub fn success_threshold_from_share_count_exec(share_count: u32) -> (t: u32)
    requires
        share_count <= 0x7FFF_FFFF,
    ensures
        t == success_threshold_from_share_count(share_count as int),
{
    threshold_from_share_count_exec(share_count) + 1
}

pub proof fn theorem_threshold_examples()
    ensures
        threshold_from_share_count(3) == 1,
        success_threshold_from_share_count(3) == 2,
        threshold_from_share_count(4) == 2,
        success_threshold_from_share_count(4) == 3,
        threshold_from_share_count(100) == 66,
        success_threshold_from_share_count(100) == 67,
        failure_threshold_from_share_count(3) == 2,
{
}

/// ExactValue uniqueness: 2 * success_threshold > n.
pub proof fn theorem_at_most_one_value_reaches_success(n: int)
    requires
        n >= 1,
    ensures
        2 * success_threshold_from_share_count(n) > n,
{
    let s = success_threshold_from_share_count(n);
    assert(2 * s > n) by (nonlinear_arith)
        requires n >= 1 && s == (2 * n - 1) / 3 + 1;
}

pub open spec fn one_in_hundredth_pips() -> int {
    1000000
}

pub open spec fn max_lp_fee() -> int {
    500000
}

pub open spec fn reduce_by_pool_fee_spec(input: int, fee: int) -> int {
    (input * (one_in_hundredth_pips() - fee)) / one_in_hundredth_pips()
}

pub proof fn theorem_reduce_by_pool_fee_bounds(input: int, fee: int)
    requires
        input >= 0,
        0 <= fee <= max_lp_fee(),
    ensures
        reduce_by_pool_fee_spec(input, fee) <= input,
        fee == 0 ==> reduce_by_pool_fee_spec(input, fee) == input,
{
    let one = one_in_hundredth_pips();
    let keep = one - fee;
    assert(0 <= keep <= one);
    assert(input * keep <= input * one) by (nonlinear_arith)
        requires 0 <= keep <= one && input >= 0;
    assert((input * keep) / one <= input) by (nonlinear_arith)
        requires 0 <= keep <= one && one > 0 && input >= 0;
    if fee == 0 {
        assert((input * one) / one == input) by (nonlinear_arith)
            requires one > 0 && input >= 0;
    }
}

} // verus!
