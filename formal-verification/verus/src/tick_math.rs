//! Mechanization of the overflow / non-zero obligations in
//! `SqrtPrice::from_tick` (amm-math/src/lib.rs ~150–220).
//!
//!   1. **No overflow:** if `0 ≤ r ≤ 2^128` and `0 < C < 2^128` then
//!      `C · r < 2^256` (justifies `U256::checked_mul` unwraps).
//!   2. **r ≠ 0:** with every bit-branch taken,
//!      `I₀ + Σ⌊log₂ Cᵢ⌋ − 19·128 = 38 ≥ 0`.
//!
//! The 19 magic constants are u128 values in the source; any `C: u128` is
//! automatically `< 2^128`. The table's ⌊log₂⌋ values are recorded below and
//! summed by the SMT/`compute` engine.

use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

pub open spec fn two_pow_128() -> int {
    pow2(128) as int
}

pub open spec fn two_pow_256() -> int {
    pow2(256) as int
}

proof fn lemma_pow2_squares()
    ensures
        pow2(128) == pow2(64) * pow2(64),
        pow2(256) == pow2(128) * pow2(128),
        pow2(64) == 0x1_0000_0000_0000_0000,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::arithmetic::power2::lemma_pow2_adds(64, 64);
    vstd::arithmetic::power2::lemma_pow2_adds(128, 128);
}

/// Any value that fits in a Rust `u128` is strictly below 2^128.
pub proof fn theorem_u128_below_two_pow_128(c: u128)
    ensures
        0 <= (c as int),
        (c as int) < (pow2(128) as int),
{
    lemma_pow2_squares();
    assert(c <= u128::MAX);
    assert((u128::MAX as int) + 1 == (pow2(128) as int)) by {
        lemma_pow2_squares();
        assert((u128::MAX as int) + 1 == (pow2(64) as int) * (pow2(64) as int)) by (compute);
    };
}

/// Obligation 1 (generic): `checked_mul` cannot overflow a 256-bit word.
pub proof fn theorem_checked_mul_no_overflow(r: int, c: int)
    requires
        0 <= r <= two_pow_128(),
        0 < c < two_pow_128(),
    ensures
        c * r < two_pow_256(),
{
    lemma_pow2_squares();
    let t128 = two_pow_128();
    let t256 = two_pow_256();
    assert(c * r <= (t128 - 1) * t128) by (nonlinear_arith)
        requires 0 <= r <= t128 && 0 < c < t128;
    assert((t128 - 1) * t128 == t128 * t128 - t128) by (nonlinear_arith)
        requires t128 > 0;
    assert(t128 * t128 == t256);
    assert(t256 - t128 < t256);
}

/// Specialisation: every `u128` constant is safe against `r ≤ 2^128`.
pub proof fn theorem_u128_const_mul_safe(r: int, c: u128)
    requires
        0 <= r <= two_pow_128(),
        c > 0,
    ensures
        (c as int) * r < two_pow_256(),
{
    theorem_u128_below_two_pow_128(c);
    theorem_checked_mul_no_overflow(r, c as int);
}

/// Known ⌊log₂ Cᵢ⌋ for the 19 `handle_tick_bit` constants.
pub open spec fn tick_constant_ilog2() -> Seq<int> {
    seq![127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 126, 125, 123, 118,
        109, 90]
}

pub open spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.skip(1))
    }
}

/// Obligation 2: worst-case MSB index after all 19 shrinks is 38 ≥ 0,
/// so `r` cannot become zero.
pub proof fn theorem_r_nonzero_msb_bound()
    ensures
        tick_constant_ilog2().len() == 19,
        sum_seq(tick_constant_ilog2()) == 2342,
        128 + sum_seq(tick_constant_ilog2()) - 19 * 128 == 38,
        128 + sum_seq(tick_constant_ilog2()) - 19 * 128 >= 0,
{
    assert(tick_constant_ilog2().len() == 19);
    assert(sum_seq(tick_constant_ilog2()) == 2342) by (compute);
    assert(128 + 2342 - 19 * 128 == 38) by (compute);
}

/// Combined statement referenced by the report.
pub proof fn theorem_from_tick_unwrap_obligations(c: u128)
    requires
        c > 0,
    ensures
        (c as int) * two_pow_128() < two_pow_256(),
        128 + sum_seq(tick_constant_ilog2()) - 19 * 128 >= 0,
{
    theorem_u128_const_mul_safe(two_pow_128(), c);
    theorem_r_nonzero_msb_bound();
}

/// Exec mirror of the 19 constants (for conformance / documentation).
pub fn tick_constants_exec() -> (v: Vec<u128>)
    ensures
        v@.len() == 19,
        forall|i: int| 0 <= i < 19 ==> v@[i] > 0,
{
    let mut v = Vec::new();
    v.push(0xfff97272373d413259a46990580e213au128);
    v.push(0xfff2e50f5f656932ef12357cf3c7fdccu128);
    v.push(0xffe5caca7e10e4e61c3624eaa0941cd0u128);
    v.push(0xffcb9843d60f6159c9db58835c926644u128);
    v.push(0xff973b41fa98c081472e6896dfb254c0u128);
    v.push(0xff2ea16466c96a3843ec78b326b52861u128);
    v.push(0xfe5dee046a99a2a811c461f1969c3053u128);
    v.push(0xfcbe86c7900a88aedcffc83b479aa3a4u128);
    v.push(0xf987a7253ac413176f2b074cf7815e54u128);
    v.push(0xf3392b0822b70005940c7a398e4b70f3u128);
    v.push(0xe7159475a2c29b7443b29c7fa6e889d9u128);
    v.push(0xd097f3bdfd2022b8845ad8f792aa5825u128);
    v.push(0xa9f746462d870fdf8a65dc1f90e061e5u128);
    v.push(0x70d869a156d2a1b890bb3df62baf32f7u128);
    v.push(0x31be135f97d08fd981231505542fcfa6u128);
    v.push(0x9aa508b5b7a84e1c677de54f3e99bc9u128);
    v.push(0x5d6af8dedb81196699c329225ee604u128);
    v.push(0x2216e584f5fa1ea926041bedfe98u128);
    v.push(0x48a170391f7dc42444e8fa2u128);
    v
}

} // verus!
