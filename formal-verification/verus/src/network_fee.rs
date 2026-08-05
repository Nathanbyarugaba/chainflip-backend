//! Verified port of the swapping pallet's network fee tracker.
//!
//! Source: state-chain/pallets/cf-swapping/src/lib.rs
//!   - `FeeRateAndMinimum`                    (~line 240)
//!   - `NetworkFeeTracker`                    (~line 260)
//!   - `NetworkFeeTracker::new`               (~line 268)
//!   - `NetworkFeeTracker::new_without_minimum` (~line 272)
//!   - `NetworkFeeTracker::take_fee`          (~line 280)
//!
//! `Permill` (rate) is represented as parts-per-million `rate_ppm <= 10^6`;
//! `Permill * u128` in sp-arithmetic computes floor(x * ppm / 10^6) without
//! intermediate overflow, which `mul_ppm` reproduces and verifies.
//!
//! Verified properties:
//!   1. `take_fee` never takes more than it is given, and splits its input
//!      exactly: `remaining_amount + fee == stable_amount` (no funds are
//!      created or destroyed).
//!   2. Panic-freedom: no overflow/underflow/division-by-zero for all inputs
//!      satisfying the stated preconditions (accumulated totals below
//!      u128::MAX, which the saturating arithmetic in the original makes
//!      explicit).
//!   3. Chunking fairness (`fee_invariant`): after any sequence of calls the
//!      accumulated fee equals `min(max(floor(rate * total), minimum), total)`
//!      - i.e. executing a swap in DCA chunks charges exactly the same total
//!      network fee as executing it in one piece; chunking can neither avoid
//!      fees nor be overcharged.

use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_multiples_vanish, lemma_fundamental_div_mod,
    lemma_hoist_over_denominator,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_commutative, lemma_mul_nonnegative,
};
use vstd::prelude::*;

verus! {

pub const MILLION: u128 = 1_000_000;

/// floor(x * ppm / 10^6) as a spec-level function.
pub open spec fn ppm_of(x: int, ppm: int) -> int {
    (x * ppm) / (MILLION as int)
}

/// The lump-sum fee for a total processed amount `total`:
/// `max(floor(rate * total), minimum)`, capped by the amount itself.
pub open spec fn lump_sum_fee(total: int, ppm: int, minimum: int) -> int {
    let uncapped = if ppm_of(total, ppm) >= minimum { ppm_of(total, ppm) } else { minimum };
    if uncapped <= total { uncapped } else { total }
}

/// Permill-style multiplication: computes floor(x * ppm / 10^6) without
/// overflowing u128 (mirrors sp_arithmetic::PerThing's overflow-free `Mul`).
pub fn mul_ppm(x: u128, ppm: u32) -> (r: u128)
    requires
        ppm <= MILLION,
    ensures
        r == ppm_of(x as int, ppm as int),
        r <= x,
{
    let q = x / MILLION;
    let rem = x % MILLION;
    proof {
        lemma_fundamental_div_mod(x as int, MILLION as int);
        // q * ppm <= q * MILLION <= x: both multiplications fit in u128.
        lemma_mul_inequality(ppm as int, MILLION as int, q as int);
        lemma_mul_is_commutative(q as int, ppm as int);
        lemma_mul_is_commutative(q as int, MILLION as int);
        assert(q * ppm <= x);
        // rem * ppm fits comfortably in u128.
        assert(rem as int * ppm as int <= MILLION as int * MILLION as int) by (nonlinear_arith)
            requires 0 <= rem as int <= MILLION as int && 0 <= ppm as int <= MILLION as int;
    }
    let high = q * (ppm as u128);
    let low = (rem * (ppm as u128)) / MILLION;
    proof {
        // (rem * ppm) / M + q * ppm == (rem * ppm + (q * ppm) * M) / M
        lemma_hoist_over_denominator(
            (rem * ppm) as int,
            (q * ppm) as int,
            MILLION as nat,
        );
        // rem * ppm + (q * ppm) * M == (q * M + rem) * ppm == x * ppm
        assert((rem * ppm) + (q * ppm) * MILLION == (q * MILLION + rem) * ppm) by (nonlinear_arith);
        lemma_ppm_bounds(x as int, ppm as int);
    }
    high + low
}

/// 0 <= floor(x * ppm / M) <= x for any 0 <= ppm <= M.
proof fn lemma_ppm_bounds(x: int, ppm: int)
    requires
        0 <= x,
        0 <= ppm <= MILLION,
    ensures
        0 <= ppm_of(x, ppm) <= x,
{
    let m = MILLION as int;
    lemma_mul_nonnegative(x, ppm);
    lemma_div_is_ordered(0, x * ppm, m);
    // x * ppm <= x * m, hence floor(x*ppm/m) <= floor(x*m/m) == x.
    lemma_mul_inequality(ppm, m, x);
    lemma_mul_is_commutative(x, ppm);
    lemma_mul_is_commutative(x, m);
    lemma_div_is_ordered(x * ppm, x * m, m);
    lemma_div_multiples_vanish(x, m);
}

/// Saturating add, mirroring `u128::saturating_add`.
pub fn sat_add(a: u128, b: u128) -> (r: u128)
    ensures
        r == if a + b <= u128::MAX { a + b } else { u128::MAX as int },
{
    if a <= u128::MAX - b { a + b } else { u128::MAX }
}

/// Saturating sub, mirroring `u128::saturating_sub`.
pub fn sat_sub(a: u128, b: u128) -> (r: u128)
    ensures
        r == if a >= b { a - b } else { 0 },
{
    if a >= b { a - b } else { 0 }
}

/// `FeeRateAndMinimum` with Permill as parts-per-million.
pub struct FeeRateAndMinimum {
    pub rate_ppm: u32,
    pub minimum: u128,
}

/// Port of `NetworkFeeTracker`.
pub struct NetworkFeeTracker {
    pub network_fee: FeeRateAndMinimum,
    /// Total amount of stable asset that has been processed so far (before fees).
    pub accumulated_stable_amount: u128,
    pub accumulated_fee: u128,
}

/// Port of `FeeTaken`.
pub struct FeeTaken {
    pub remaining_amount: u128,
    pub fee: u128,
}

impl NetworkFeeTracker {
    /// Structural well-formedness + the chunking-fairness invariant: the fee
    /// accumulated so far is exactly the lump-sum fee of the amount processed
    /// so far.
    pub open spec fn wf(&self) -> bool {
        &&& self.network_fee.rate_ppm <= MILLION
        &&& self.accumulated_fee == lump_sum_fee(
            self.accumulated_stable_amount as int,
            self.network_fee.rate_ppm as int,
            self.network_fee.minimum as int,
        )
    }

    /// Port of `NetworkFeeTracker::new`.
    pub fn new(rate_ppm: u32, minimum: u128) -> (r: Self)
        requires
            rate_ppm <= MILLION,
        ensures
            r.wf(),
            r.accumulated_stable_amount == 0,
            r.accumulated_fee == 0,
            r.network_fee.rate_ppm == rate_ppm,
            r.network_fee.minimum == minimum,
    {
        proof {
            assert(ppm_of(0, rate_ppm as int) == 0) by (nonlinear_arith);
        }
        Self {
            network_fee: FeeRateAndMinimum { rate_ppm, minimum },
            accumulated_stable_amount: 0,
            accumulated_fee: 0,
        }
    }

    /// Port of `NetworkFeeTracker::new_without_minimum`.
    pub fn new_without_minimum(rate_ppm: u32, _minimum: u128) -> (r: Self)
        requires
            rate_ppm <= MILLION,
        ensures
            r.wf(),
            r.accumulated_stable_amount == 0,
            r.accumulated_fee == 0,
            r.network_fee.rate_ppm == rate_ppm,
            r.network_fee.minimum == 0,
    {
        Self::new(rate_ppm, 0)
    }

    /// Port of `NetworkFeeTracker::take_fee`.
    ///
    /// The precondition `accumulated_stable_amount + stable_amount <= u128::MAX`
    /// rules out saturation of the accumulators (unreachable in practice:
    /// amounts are bounded by total asset issuance); with it, every
    /// `saturating_*` in the original behaves like exact arithmetic and the
    /// fairness invariant is preserved exactly.
    pub fn take_fee(&mut self, stable_amount: u128) -> (r: FeeTaken)
        requires
            old(self).wf(),
            old(self).accumulated_stable_amount + stable_amount <= u128::MAX,
        ensures
            final(self).wf(),
            // No funds created or destroyed; fee never exceeds the input.
            r.fee <= stable_amount,
            r.remaining_amount + r.fee == stable_amount,
            // Accumulator updates are exact.
            final(self).accumulated_stable_amount == old(self).accumulated_stable_amount
                + stable_amount,
            final(self).accumulated_fee == old(self).accumulated_fee + r.fee,
            // Rate configuration is unchanged.
            final(self).network_fee.rate_ppm == old(self).network_fee.rate_ppm,
            final(self).network_fee.minimum == old(self).network_fee.minimum,
    {
        if stable_amount == 0 {
            return FeeTaken { remaining_amount: 0, fee: 0 };
        }

        let ppm = self.network_fee.rate_ppm;
        let minimum = self.network_fee.minimum;
        let acc_stable = self.accumulated_stable_amount;
        let acc_fee = self.accumulated_fee;

        let new_total = sat_add(acc_stable, stable_amount);
        let rated = mul_ppm(new_total, ppm);
        let calculated_fee = if rated >= minimum { rated } else { minimum };

        let fee_taken = {
            let due = sat_sub(calculated_fee, acc_fee);
            if due <= stable_amount { due } else { stable_amount }
        };

        proof {
            lemma_take_fee_preserves_invariant(
                acc_stable as int,
                stable_amount as int,
                ppm as int,
                minimum as int,
                acc_fee as int,
            );
        }

        self.accumulated_fee = sat_add(acc_fee, fee_taken);
        self.accumulated_stable_amount = sat_add(acc_stable, stable_amount);

        FeeTaken { remaining_amount: stable_amount - fee_taken, fee: fee_taken }
    }
}

/// Monotonicity of the rated fee in the processed amount.
proof fn lemma_ppm_monotone(x: int, y: int, ppm: int)
    requires
        0 <= x <= y,
        0 <= ppm,
    ensures
        ppm_of(x, ppm) <= ppm_of(y, ppm),
{
    lemma_mul_inequality(x, y, ppm);
    lemma_div_is_ordered(x * ppm, y * ppm, MILLION as int);
}

/// The rated fee grows by at most the amount added: for ppm <= 10^6,
/// floor(ppm*(s+a)/M) <= floor(ppm*s/M) + a.
proof fn lemma_ppm_lipschitz(s: int, a: int, ppm: int)
    requires
        0 <= s,
        0 <= a,
        0 <= ppm <= MILLION,
    ensures
        ppm_of(s + a, ppm) <= ppm_of(s, ppm) + a,
{
    let m = MILLION as int;
    // (s+a)*ppm == s*ppm + a*ppm <= s*ppm + a*m
    assert((s + a) * ppm == s * ppm + a * ppm) by (nonlinear_arith);
    lemma_mul_inequality(ppm, m, a);
    lemma_mul_is_commutative(a, ppm);
    lemma_mul_is_commutative(a, m);
    lemma_div_is_ordered((s + a) * ppm, s * ppm + a * m, m);
    // (s*ppm + a*m)/m == s*ppm/m + a
    lemma_hoist_over_denominator(s * ppm, a, m as nat);
}

/// The heart of the chunking-fairness argument: one `take_fee` step preserves
/// the lump-sum-fee invariant, and the fee taken is exactly the difference of
/// consecutive lump sums.
proof fn lemma_take_fee_preserves_invariant(s: int, a: int, ppm: int, minimum: int, acc_fee: int)
    requires
        0 <= s,
        1 <= a,
        0 <= ppm <= MILLION,
        0 <= minimum,
        acc_fee == lump_sum_fee(s, ppm, minimum),
    ensures
        ({
            let calc = if ppm_of(s + a, ppm) >= minimum { ppm_of(s + a, ppm) } else { minimum };
            let due = if calc >= acc_fee { calc - acc_fee } else { 0 };
            let fee = if due <= a { due } else { a };
            acc_fee + fee == lump_sum_fee(s + a, ppm, minimum)
        }),
{
    lemma_ppm_monotone(s, s + a, ppm);
    lemma_ppm_lipschitz(s, a, ppm);
    lemma_ppm_bounds(s, ppm);
    lemma_ppm_bounds(s + a, ppm);
}

} // verus!
