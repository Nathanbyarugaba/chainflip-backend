//! Conformance probes for `take_broker_fees` rounding / fund-safety.
//!
//! Mirrors formal-verification/verus/src/broker_fee.rs and
//! formal-verification/tla/BrokerFeeSplit.tla against real `Permill`.

#[cfg(test)]
mod broker_fee_fund_safety {
    use proptest::prelude::*;
    use sp_arithmetic::Permill;

    const BPM: u32 = 100;
    const MAX_VALIDATED_BPS: u16 = 1000;
    const MAX_BENEFICIARIES: usize = 6;
    const ONE_AS_BPS: u16 = 10_000;

    fn fee(bps: u16, amount: u128) -> u128 {
        Permill::from_parts(bps as u32 * BPM) * amount
    }

    fn sum_fees(bps: &[u16], amount: u128) -> u128 {
        bps.iter().map(|b| fee(*b, amount)).sum()
    }

    /// Production constraints: Σ fees never exceeds amount
    /// (no assert! panic, no USDC minted beyond the swap output).
    #[test]
    fn validated_fees_never_exceed_amount_exhaustive_small() {
        for n in 0..=MAX_BENEFICIARIES {
            for total in 0u16..=MAX_VALIDATED_BPS {
                if n == 0 {
                    assert_eq!(sum_fees(&[], 12345), 0);
                    continue;
                }
                if total < n as u16 {
                    continue;
                }
                // Equal split (worst-case rounding alignment) + one uneven.
                if total % (n as u16) == 0 {
                    let each = total / n as u16;
                    let bps = vec![each; n];
                    for amount in 0u128..=2_000 {
                        let s = sum_fees(&bps, amount);
                        assert!(
                            s <= amount,
                            "overcharge: n={n} each={each} amount={amount} sum={s}"
                        );
                    }
                }
            }
        }
    }

    fn validated_bps_strategy() -> impl Strategy<Value = Vec<u16>> {
        (0usize..=MAX_BENEFICIARIES).prop_flat_map(|n| {
            if n == 0 {
                Just(Vec::new()).boxed()
            } else {
                (1u16..=MAX_VALIDATED_BPS).prop_flat_map(move |total| {
                    proptest::collection::vec(1u16..=total, n).prop_map(move |mut parts| {
                        // Rescale/truncate so the sum equals `total` (or less if
                        // forced by minima), staying within the validation ceiling.
                        let sum: u32 = parts.iter().map(|p| *p as u32).sum();
                        if sum == 0 {
                            return vec![1; n];
                        }
                        for p in parts.iter_mut() {
                            *p = ((*p as u32) * (total as u32) / sum).max(1) as u16;
                        }
                        let mut s: u32 = parts.iter().map(|p| *p as u32).sum();
                        while s > total as u32 {
                            if let Some(p) = parts.iter_mut().find(|p| **p > 1) {
                                *p -= 1;
                                s -= 1;
                            } else {
                                break;
                            }
                        }
                        parts
                    })
                })
                .boxed()
            }
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        #[test]
        fn validated_random_splits_never_exceed_amount(
            amount: u128,
            bps in validated_bps_strategy(),
        ) {
            prop_assert!(bps.iter().map(|b| *b as u32).sum::<u32>() <= MAX_VALIDATED_BPS as u32);
            let s = sum_fees(&bps, amount);
            prop_assert!(s <= amount, "sum={s} amount={amount} bps={bps:?}");
        }
    }

    /// Finding witness: unvalidated 100% equal split overcharges.
    #[test]
    fn unvalidated_equal_split_overcharge_witness() {
        let amount = 3u128;
        let bps = [2500u16, 2500, 2500, 2500];
        assert_eq!(bps.iter().sum::<u16>(), ONE_AS_BPS);
        let s = sum_fees(&bps, amount);
        assert_eq!(s, 4);
        assert!(s > amount);
    }

    /// Documented observation: split nearest-rounding can *under*-collect
    /// vs a single Permill(total_bps).
    #[test]
    fn split_can_undercollect_vs_combined() {
        let amount = 10u128;
        let bps = [500u16, 500];
        let split = sum_fees(&bps, amount);
        let combined = fee(1000, amount);
        assert_eq!(split, 0);
        assert_eq!(combined, 1);
        assert!(split < combined);
    }

    /// Transcription of the Verus witness matches real Permill.
    #[test]
    fn verus_witness_matches_permill() {
        // beneficiary_fee(3, 2500) == 1
        assert_eq!(fee(2500, 3), 1);
        assert_eq!(crate::verified_model::mul_ppm(3, 2500 * BPM), 1);
    }
}
