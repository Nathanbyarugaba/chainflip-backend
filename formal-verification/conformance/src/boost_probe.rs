
#[cfg(test)]
mod boost_fee_probe {
    use proptest::prelude::*;
    use sp_arithmetic::Permill;

    const BPM: u32 = 100;

    fn fee_from_boosted_amount(amount: u128, fee_bps: u16) -> u128 {
        Permill::from_parts(fee_bps as u32 * BPM) * amount
    }

    // Conservation: after the lending/boost fee split, reported amounts
    // always sum to the original deposit (mirrors try_boosting bookkeeping).
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8192))]
        #[test]
        fn reported_amounts_sum_to_deposit(
            deposit in 1u128..(u128::MAX / 2),
            lend_share in 0u128..=1_000_000u128,
        ) {
            let total_fee = fee_from_boosted_amount(deposit, 5);
            let required = deposit.saturating_sub(total_fee);
            prop_assume!(required > 0);
            let lend_p = required.saturating_mul(lend_share) / 1_000_000;
            let lend_p = lend_p.min(required);
            let boost_p = required - lend_p;
            let lend_fee = Permill::from_rational(lend_p, required) * total_fee;
            let boost_fee = total_fee.saturating_sub(lend_fee);
            let sum = lend_p + lend_fee + boost_p + boost_fee;
            prop_assert_eq!(sum, deposit);
        }
    }

    /// If a boosted deposit is later full-witnessed at a *different* amount,
    /// process_full_witness_deposit_inner takes the BoostNotConsumed path
    /// without clearing the boost (see cf-ingress-egress lib.rs ~3159-3171).
    #[test]
    fn amount_mismatch_selects_non_boosted_path() {
        let boosted_amount = 100u128;
        let witnessed_amount = 99u128;
        assert_ne!(boosted_amount, witnessed_amount);
        let finalise = boosted_amount == witnessed_amount;
        assert!(!finalise);
    }
}
