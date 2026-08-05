//! Verified mul-div kernel: floor and ceil of `a * b / c` with a full-width
//! intermediate product.
//!
//! Source contract mirrored: state-chain/amm-math/src/lib.rs
//!   - `mul_div_floor_ceil`   (~line 373): floor/ceil of a*b/c in U512 space,
//!     `None` iff c == 0
//!   - `mul_div_floor_checked` (~line 387): floor, `None` also when the
//!     result does not fit the output width
//!   - `mul_div_ceil_checked`  (~line 391): ceil, likewise
//!
//! The port works at u128 width (the verified algorithm computes the exact
//! 256-bit product a*b and divides it by c), which is structurally identical
//! to the U256-with-U512-intermediate original: the same "multiply full
//! width, divide, check the result fits" contract, two limbs down. The
//! conformance suite (../conformance/) checks the *original* U256 functions
//! against the same mathematical specification that is proven here.
//!
//! Verified properties (for all inputs, machine-checked):
//!   1. `full_mul` computes the exact 256-bit product: hi*2^128 + lo == a*b.
//!   2. `mul_div_floor(a, b, c) == Some(q)` iff c != 0 and floor(a*b/c) fits
//!      u128, and then q == floor(a*b/c) exactly; `None` iff c == 0 or
//!      overflow. This mechanizes the overflow-safety comment in
//!      `mul_div_floor_ceil` ("Cannot overflow as ...").
//!   3. `mul_div_ceil` likewise for ceil(a*b/c) == floor + (rem != 0).
//!   4. Panic-freedom: no division by zero, no arithmetic overflow, and the
//!      256-iteration long division terminates.

use vstd::arithmetic::div_mod::{
    lemma_div_denominator, lemma_div_pos_is_pos, lemma_fundamental_div_mod,
    lemma_fundamental_div_mod_converse, lemma_mod_bound,
};
use vstd::arithmetic::power2::{lemma_pow2_adds, pow2};
use vstd::prelude::*;

verus! {

/// 2^64 (limb base for the schoolbook multiplication).
pub const TWO64: u128 = 0x1_0000_0000_0000_0000;

/// 2^127 (starting bit mask, as a divisor, for the long division).
pub const TWO127: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000;

/// Exact 256-bit product of two u128s as (hi, lo) limbs:
/// hi * 2^128 + lo == a * b.
///
/// Mirrors `U256::full_mul` (four u64 partial products with carries), the
/// primitive used by `mul_div_floor_ceil`.
pub fn full_mul(a: u128, b: u128) -> (r: (u128, u128))
    ensures
        r.0 * pow2(128) + r.1 == a * b,
{
    let a1 = a / TWO64;
    let a0 = a % TWO64;
    let b1 = b / TWO64;
    let b0 = b % TWO64;
    proof {
        lemma_fundamental_div_mod(a as int, TWO64 as int);
        lemma_fundamental_div_mod(b as int, TWO64 as int);
        lemma_div_bound_128(a as int);
        lemma_div_bound_128(b as int);
        // All four partial products fit in u128.
        assert(a1 * b1 < TWO64 * TWO64 && a0 * b1 < TWO64 * TWO64 && a1 * b0 < TWO64 * TWO64
            && a0 * b0 < TWO64 * TWO64) by (nonlinear_arith)
            requires
                0 <= a1 < TWO64 && 0 <= a0 < TWO64 && 0 <= b1 < TWO64 && 0 <= b0 < TWO64;
    }
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;

    let u0 = p00 / TWO64;
    let l0 = p00 % TWO64;
    let h01 = p01 / TWO64;
    let l01 = p01 % TWO64;
    let h10 = p10 / TWO64;
    let l10 = p10 % TWO64;
    let h11 = p11 / TWO64;
    let l11 = p11 % TWO64;
    proof {
        lemma_div_bound_128(p00 as int);
        lemma_div_bound_128(p01 as int);
        lemma_div_bound_128(p10 as int);
        lemma_div_bound_128(p11 as int);
    }

    // Column sums with carries; each fits u128 comfortably (<= 3 * 2^64).
    let t1 = u0 + l01 + l10;
    let limb1 = t1 % TWO64;
    let carry1 = t1 / TWO64;
    let t2 = carry1 + h01 + h10 + l11;
    let limb2 = t2 % TWO64;
    let carry2 = t2 / TWO64;
    let t3 = carry2 + h11;

    proof {
        lemma_fundamental_div_mod(p00 as int, TWO64 as int);
        lemma_fundamental_div_mod(p01 as int, TWO64 as int);
        lemma_fundamental_div_mod(p10 as int, TWO64 as int);
        lemma_fundamental_div_mod(p11 as int, TWO64 as int);
        lemma_fundamental_div_mod(t1 as int, TWO64 as int);
        lemma_fundamental_div_mod(t2 as int, TWO64 as int);

        let two64 = TWO64 as int;
        let two128 = two64 * two64;
        let two192 = two128 * two64;

        // Expand a*b over the u64 limbs.
        assert(a * b == p11 * two128 + (p01 + p10) * two64 + p00) by (nonlinear_arith)
            requires
                a == a1 * two64 + a0 && b == b1 * two64 + b0 && p00 == a0 * b0
                    && p01 == a0 * b1 && p10 == a1 * b0 && p11 == a1 * b1
                    && two128 == two64 * two64;

        // Substitute the div/mod decompositions and regroup into the output
        // limbs. Pure ring reasoning, staged for the solver.
        assert(p11 * two128 + (p01 + p10) * two64 + p00 == (t3 * two64 + limb2) * two128 + (
        limb1 * two64 + l0)) by (nonlinear_arith)
            requires
                p00 == u0 * two64 + l0 && p01 == h01 * two64 + l01 && p10 == h10 * two64 + l10
                    && p11 == h11 * two64 + l11 && t1 == u0 + l01 + l10 && t1 == carry1 * two64
                    + limb1 && t2 == carry1 + h01 + h10 + l11 && t2 == carry2 * two64 + limb2
                    && t3 == carry2 + h11 && two128 == two64 * two64;

        // The high limb pair fits u128: hi * 2^128 <= a * b < 2^256.
        assert(a * b < two128 * two128) by (nonlinear_arith)
            requires
                0 <= a < two128 && 0 <= b < two128 && two128 == two64 * two64;
        assert(t3 * two64 + limb2 < two128) by (nonlinear_arith)
            requires
                (t3 * two64 + limb2) * two128 + (limb1 * two64 + l0) == a * b,
                a * b < two128 * two128,
                0 <= limb1 * two64 + l0,
                0 <= t3 * two64 + limb2,
                two128 > 0;
        assert(0 <= t3 * two64 + limb2) by (nonlinear_arith)
            requires t3 >= 0 && limb2 >= 0 && two64 > 0;
        // Low limb pair fits: limb1 < 2^64 and l0 < 2^64.
        assert(limb1 * two64 + l0 < two128) by (nonlinear_arith)
            requires 0 <= limb1 < two64 && 0 <= l0 < two64 && two128 == two64 * two64;

        lemma_pow2_128();
    }
    let hi = t3 * TWO64 + limb2;
    let lo = limb1 * TWO64 + l0;
    (hi, lo)
}

/// Long division of the 256-bit value hi*2^128 + lo by c (bit-by-bit,
/// mirroring the shift-subtract structure of U512 division): returns the
/// quotient (if it fits u128) and the remainder.
///
/// Returns (overflow, q, r) with:
///   - overflow == true iff (hi*2^128 + lo) / c >= 2^128
///   - !overflow ==> q == (hi*2^128 + lo) / c
///   - r == (hi*2^128 + lo) % c
pub fn div_256_by_128(hi: u128, lo: u128, c: u128) -> (res: (bool, u128, u128))
    requires
        c >= 1,
    ensures
        ({
            let d = hi * pow2(128) + lo;
            &&& (res.0 <==> d / (c as int) >= pow2(128))
            &&& (!res.0 ==> res.1 == d / (c as int))
            &&& res.2 == d % (c as int)
        }),
{
    let ghost d: int = hi * pow2(128) + lo;

    let mut overflow: bool = false;
    let mut q: u128 = 0;
    let mut r: u128 = 0;
    let ghost mut qg: int = 0;
    // prefix == the value of the bits of d processed so far.
    let ghost mut prefix: int = 0;

    proof {
        lemma_pow2_128();
        lemma_pow2_128();
    }

    // ---- process the 128 bits of `hi` ----
    let mut p: u128 = TWO127;
    let ghost mut j: nat = 0;
    proof {
        lemma_pow2_128();
        assert(hi as int / (pow2(127) * 2) as int == 0) by {
            lemma_pow2_128();
            assert(pow2(127) * 2 == pow2(128)) by {
                lemma_pow2_adds(127, 1);
                lemma_pow2_128();
            }
            assert(hi < pow2(128));
        }
    }
    while p > 0
        invariant
            c >= 1,
            j <= 128,
            p > 0 ==> j < 128 && p == pow2((127 - j) as nat),
            p == 0 ==> j == 128,
            prefix == hi as int / (if p > 0 { (pow2((127 - j) as nat) * 2) as int } else { 1int }),
            prefix == qg * c + r,
            0 <= r < c,
            qg >= 0,
            overflow <==> qg >= pow2(128),
            !overflow ==> q == qg,
        decreases p,
    {
        let bit = (hi / p) % 2;
        proof {
            lemma_bit_extraction(hi as int, p as int, (127 - j) as nat);
        }
        let (qg1, prefix1) = div_step(&mut overflow, &mut q, &mut r, bit, c, Ghost(qg), Ghost(prefix));
        proof {
            qg = qg1@;
            prefix = prefix1@;
        }
        proof {
            if j < 127 {
                lemma_pow2_halves((127 - j) as nat);
            } else {
                assert(p == pow2(0));
                lemma_pow2_128();
            }
            j = j + 1;
        }
        p = p / 2;
    }
    proof {
        assert(prefix == hi as int);
    }

    // ---- process the 128 bits of `lo` ----
    let mut p2: u128 = TWO127;
    let ghost mut k: nat = 0;
    proof {
        lemma_pow2_128();
        assert(lo as int / (pow2(127) * 2) as int == 0) by {
            lemma_pow2_128();
            assert(pow2(127) * 2 == pow2(128)) by {
                lemma_pow2_adds(127, 1);
                lemma_pow2_128();
            }
            assert(lo < pow2(128));
        }
        assert(prefix == hi as int * pow2(0) + lo as int / (pow2(127) * 2) as int) by {
            lemma_pow2_128();
        }
    }
    while p2 > 0
        invariant
            c >= 1,
            k <= 128,
            p2 > 0 ==> k < 128 && p2 == pow2((127 - k) as nat),
            p2 == 0 ==> k == 128,
            prefix == hi as int * pow2(k) + lo as int / (if p2 > 0 {
                (pow2((127 - k) as nat) * 2) as int
            } else {
                1int
            }),
            prefix == qg * c + r,
            0 <= r < c,
            qg >= 0,
            overflow <==> qg >= pow2(128),
            !overflow ==> q == qg,
        decreases p2,
    {
        let bit = (lo / p2) % 2;
        proof {
            lemma_bit_extraction(lo as int, p2 as int, (127 - k) as nat);
            // prefix' = 2*prefix + bit = hi*2^(k+1) + (2*lo_prefix + bit).
            lemma_pow2_adds(k, 1);
            lemma_pow2_128();
            assert(hi as int * pow2(k + 1) == 2 * (hi as int * pow2(k))) by (nonlinear_arith)
                requires
                    pow2(k + 1) == pow2(k) * pow2(1) && pow2(1) == 2;
        }
        let (qg1, prefix1) = div_step(&mut overflow, &mut q, &mut r, bit, c, Ghost(qg), Ghost(prefix));
        proof {
            qg = qg1@;
            prefix = prefix1@;
        }
        proof {
            if k < 127 {
                lemma_pow2_halves((127 - k) as nat);
            } else {
                assert(p2 == pow2(0));
                lemma_pow2_128();
            }
            k = k + 1;
        }
        p2 = p2 / 2;
    }

    proof {
        assert(prefix == d);
        lemma_fundamental_div_mod_converse(d, c as int, qg, r as int);
    }
    (overflow, q, r)
}

/// One shift-subtract division step: prefix' = 2*prefix + bit, updating
/// quotient and remainder so prefix' == qg'*c + r' with r' < c.
fn div_step(
    overflow: &mut bool,
    q: &mut u128,
    r: &mut u128,
    bit: u128,
    c: u128,
    qg0: Ghost<int>,
    prefix0: Ghost<int>,
) -> (out: (Ghost<int>, Ghost<int>))  // (qg', prefix')
    requires
        c >= 1,
        bit <= 1,
        prefix0@ == qg0@ * c + *old(r),
        0 <= *old(r) < c,
        qg0@ >= 0,
        *old(overflow) <==> qg0@ >= pow2(128),
        !*old(overflow) ==> *old(q) == qg0@,
    ensures
        out.1@ == 2 * prefix0@ + bit,
        out.1@ == out.0@ * c + *final(r),
        0 <= *final(r) < c,
        out.0@ >= 0,
        (*final(overflow) <==> out.0@ >= pow2(128)),
        !*final(overflow) ==> *final(q) == out.0@,
{
    proof {
        lemma_pow2_128();
    }
    let ghost r_old: int = *r as int;
    // r' = 2r + bit, subtracting c once if the result reaches c.
    let qbit: u128;
    if *r >= TWO127 {
        // 2r + bit >= 2^128 > c - wait, c can be up to 2^128 - 1; but
        // 2r >= 2^128 > c always holds since c <= u128::MAX < 2^128.
        // Subtraction is certain; compute 2r + bit - c without overflow:
        // 2r + bit - c == (r - (c - r)) + bit, and r >= c - r since 2r >= c.
        proof {
            let r_now = *r as int;
            assert(2 * r_now + bit - c < c) by (nonlinear_arith)
                requires r_now < c && bit <= 1 && 2 * r_now >= c;
        }
        let diff = c - *r;
        // diff == c - r (c > r always).
        *r = (*r - diff) + bit;
        qbit = 1;
    } else {
        let doubled = *r * 2 + bit;
        if doubled >= c {
            *r = doubled - c;
            qbit = 1;
        } else {
            *r = doubled;
            qbit = 0;
        }
    }
    let ghost prefix1: int = 2 * prefix0@ + bit;
    let ghost qg1: int = 2 * qg0@ + qbit;
    proof {
        let r_new = *r as int;
        assert(prefix1 == qg1 * c + r_new) by (nonlinear_arith)
            requires
                prefix0@ == qg0@ * c + r_old,
                prefix1 == 2 * prefix0@ + bit,
                qg1 == 2 * qg0@ + qbit,
                qbit == 0 || qbit == 1,
                (qbit == 1 ==> r_new == 2 * r_old + bit - c),
                (qbit == 0 ==> r_new == 2 * r_old + bit);
    }
    // Track quotient overflow: qg' = 2*qg + qbit >= 2^128 iff (already
    // overflowed) or q >= 2^127.
    if !*overflow {
        if *q >= TWO127 {
            *overflow = true;
            proof {
                lemma_pow2_128();
                assert(qg1 >= pow2(128)) by {
                    lemma_pow2_halves(128);
                }
            }
        } else {
            proof {
                lemma_pow2_128();
                assert(qg1 < pow2(128)) by {
                    lemma_pow2_halves(128);
                }
            }
            *q = *q * 2 + qbit;
        }
    } else {
        proof {
            assert(qg1 >= pow2(128));
        }
    }
    (Ghost(qg1), Ghost(prefix1))
}

/// Mirrors `mul_div_floor_checked`: Some(floor(a*b/c)) unless c == 0 or the
/// floor does not fit the output width.
pub fn mul_div_floor(a: u128, b: u128, c: u128) -> (res: Option<u128>)
    ensures
        c == 0 ==> res is None,
        c > 0 ==> {
            let exact = (a * b) / (c as int);
            &&& (res is Some <==> exact < pow2(128))
            &&& (res is Some ==> res->Some_0 == exact)
        },
{
    if c == 0 {
        return None;
    }
    let (hi, lo) = full_mul(a, b);
    let (overflow, q, _r) = div_256_by_128(hi, lo, c);
    if overflow {
        None
    } else {
        Some(q)
    }
}

/// Mirrors `mul_div_ceil_checked`: Some(ceil(a*b/c)) unless c == 0 or the
/// ceil does not fit the output width. The "cannot overflow" comment in
/// `mul_div_floor_ceil` (floor + 1 requires a nonzero remainder, hence
/// floor < a*b/c <= max) is mechanized by the q < 2^128 - 1 case analysis.
pub fn mul_div_ceil(a: u128, b: u128, c: u128) -> (res: Option<u128>)
    ensures
        c == 0 ==> res is None,
        c > 0 ==> {
            let exact = (a * b) / (c as int);
            let rem = (a * b) % (c as int);
            let ceil = if rem == 0 { exact } else { exact + 1 };
            &&& (res is Some <==> ceil < pow2(128))
            &&& (res is Some ==> res->Some_0 == ceil)
        },
{
    if c == 0 {
        return None;
    }
    let (hi, lo) = full_mul(a, b);
    let (overflow, q, r) = div_256_by_128(hi, lo, c);
    proof {
        lemma_pow2_128();
    }
    if overflow {
        None
    } else if r == 0 {
        Some(q)
    } else if q == u128::MAX {
        None
    } else {
        Some(q + 1)
    }
}

// ---------------------------------------------------------------------------
// Arithmetic helper lemmas
// ---------------------------------------------------------------------------

/// Concrete values for the powers of two used throughout this module.
proof fn lemma_pow2_128()
    ensures
        pow2(0) == 1,
        pow2(1) == 2,
        pow2(64) == TWO64,
        pow2(127) == TWO127,
        pow2(128) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
        pow2(128) == TWO64 * TWO64,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    lemma_pow2_adds(64, 63);
    lemma_pow2_adds(64, 64);
    assert(pow2(127) == pow2(64) * pow2(63));
    // lemma2_to64 provides the literal values of pow2(63) and pow2(64);
    // the product of the two literals is constant-folded by the solver.
    assert(pow2(64) * pow2(63) == TWO127) by (nonlinear_arith)
        requires
            pow2(64) == 0x1_0000_0000_0000_0000 && pow2(63) == 0x8000_0000_0000_0000;
}

/// x / 2^64 < 2^64 for x < 2^128.
proof fn lemma_div_bound_128(x: int)
    requires
        0 <= x < TWO64 * TWO64,
    ensures
        0 <= x / (TWO64 as int) < TWO64,
        0 <= x % (TWO64 as int) < TWO64,
{
    lemma_fundamental_div_mod(x, TWO64 as int);
    lemma_mod_bound(x, TWO64 as int);
    lemma_div_pos_is_pos(x, TWO64 as int);
    assert(x / (TWO64 as int) < TWO64) by (nonlinear_arith)
        requires
            x == TWO64 as int * (x / (TWO64 as int)) + x % (TWO64 as int),
            0 <= x % (TWO64 as int),
            x < TWO64 * TWO64,
            x / (TWO64 as int) >= 0;
}

/// pow2(n)/2 == pow2(n-1) for n >= 1.
proof fn lemma_pow2_halves(n: nat)
    requires
        n >= 1,
    ensures
        pow2(n) / 2 == pow2((n - 1) as nat),
        pow2(n) == 2 * pow2((n - 1) as nat),
{
    lemma_pow2_adds((n - 1) as nat, 1);
    lemma_pow2_128();
}

/// Bit-extraction step: with p == 2^m, extracting bit m of x advances the
/// processed prefix from floor(x / 2^(m+1)) to floor(x / 2^m):
/// floor(x/2^m) == 2*floor(x/2^(m+1)) + ((x/2^m) % 2).
proof fn lemma_bit_extraction(x: int, p: int, m: nat)
    requires
        p == pow2(m),
        0 <= x,
    ensures
        x / (pow2(m) as int) == 2 * (x / (pow2(m) * 2) as int) + (x / p) % 2,
        0 <= (x / p) % 2 <= 1,
{
    let p_int = pow2(m) as int;
    assert(p_int > 0) by {
        vstd::arithmetic::power2::lemma_pow2_pos(m);
    }
    // x / (2^m * 2) == (x / 2^m) / 2
    lemma_div_denominator(x, p_int, 2);
    // x/2^m == 2*((x/2^m)/2) + (x/2^m)%2
    lemma_fundamental_div_mod(x / p_int, 2);
    lemma_mod_bound(x / p_int, 2);
    lemma_div_pos_is_pos(x, p_int);
}

} // verus!
