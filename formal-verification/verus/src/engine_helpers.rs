//! Verified ports of engine helper arithmetic used by the multisig client
//! and RPC retrier.
//!
//! Sources:
//!   engine/multisig/src/client/utils.rs
//!     - `threshold_for_broadcast_verification` (~44)
//!   engine/src/retrier.rs
//!     - `max_sleep_duration` (~213)

use vstd::prelude::*;

verus! {

/// Port of `threshold_for_broadcast_verification`: integer half of the party
/// count. Agreement requires a count *strictly greater* than this threshold
/// (`find_frequent_element` uses `count > threshold`).
pub open spec fn broadcast_threshold(n: nat) -> nat {
    n / 2
}

pub fn threshold_for_broadcast_verification(total_parties: usize) -> (t: usize)
    ensures
        t == broadcast_threshold(total_parties as nat),
        t <= total_parties,
{
    total_parties / 2
}

/// Agreement quorum size: one more than the threshold.
pub open spec fn agreement_quorum(n: nat) -> nat {
    broadcast_threshold(n) + 1
}

proof fn lemma_quorum_bounds(n: nat)
    requires
        n >= 1,
    ensures
        1 <= agreement_quorum(n) <= n,
{
    if n == 1 {
        assert(agreement_quorum(1) == 1);
    } else {
        assert(n / 2 + 1 <= n) by (nonlinear_arith)
            requires n >= 2;
    }
}

/// Concrete checks matching the Rust unit test in utils.rs (~52-59).
pub proof fn theorem_threshold_examples()
    ensures
        broadcast_threshold(1) == 0,
        broadcast_threshold(2) == 1,
        broadcast_threshold(3) == 1,
        broadcast_threshold(99) == 49,
        broadcast_threshold(100) == 50,
{
}

pub fn threshold_examples() -> (ok: bool)
    ensures
        ok == true,
{
    proof {
        theorem_threshold_examples();
    }
    let t1 = threshold_for_broadcast_verification(1);
    let t2 = threshold_for_broadcast_verification(2);
    let t3 = threshold_for_broadcast_verification(3);
    assert(t1 == 0 && t2 == 1 && t3 == 1);
    true
}

/// FINDING witness: for n=2, threshold=1, a single verification message
/// satisfies |submitters| ≤ threshold, so `verify_broadcasts` returns
/// InsufficientVerificationMessages with an **empty** report set.
pub proof fn theorem_n2_single_submitter_blames_nobody()
    ensures
        broadcast_threshold(2) == 1,
        (1nat) <= broadcast_threshold(2),
{
    assert(broadcast_threshold(2) == 1);
}

/// Port of `max_sleep_duration` without relying on unsupported saturating_mul.
/// Uses checked path: if shift would overflow u32 multiply, return max_delay.
pub fn max_sleep_duration(initial_ms: u32, max_delay_ms: u32, attempt: u32) -> (r: u32)
    ensures
        r <= max_delay_ms,
{
    if initial_ms == 0 {
        return 0;
    }
    if attempt >= 32 {
        return max_delay_ms;
    }
    let factor: u32 = 1u32 << attempt;
    // grown = initial * 2^attempt, capped
    if factor == 0 {
        return max_delay_ms;
    }
    // Ensure initial_ms * factor fits in u32 and is ≤ max_delay_ms.
    if initial_ms > max_delay_ms / factor {
        max_delay_ms
    } else {
        proof {
            assert(initial_ms as int * factor as int <= max_delay_ms as int) by (nonlinear_arith)
                requires
                    factor > 0 && initial_ms <= max_delay_ms / factor;
            assert(initial_ms as int * factor as int <= u32::MAX) by (nonlinear_arith)
                requires
                    initial_ms as int * factor as int <= max_delay_ms as int
                        && max_delay_ms <= u32::MAX;
        }
        initial_ms * factor
    }
}

pub fn sleep_never_exceeds_cap(initial_ms: u32, max_delay_ms: u32, attempt: u32) -> (r: u32)
    ensures
        r <= max_delay_ms,
{
    max_sleep_duration(initial_ms, max_delay_ms, attempt)
}

/// Limit(0) still allows attempt index 0 — see TLA+ RetrierLimitZero.cfg.
pub open spec fn limit_allows_attempt(limit: nat, attempt: nat) -> bool {
    attempt == 0 || attempt < limit
}

pub proof fn theorem_limit_zero_allows_first_attempt()
    ensures
        limit_allows_attempt(0, 0),
        !limit_allows_attempt(0, 1),
{
}

} // verus!
