//! Conformance suite binding the formally verified models in
//! `formal-verification/verus/` to the shipped state-chain code.
//!
//! Three layers of binding (see ../REPORT.md for the full trust argument):
//!
//! 1. **Spec conformance**: `cf_amm_math::mul_div_floor_checked` /
//!    `mul_div_ceil_checked` (the real U256 implementations) are property-
//!    tested against the *same mathematical specification* that the Verus
//!    kernel `verus/src/mul_div.rs` is proven to satisfy
//!    (floor/ceil of the exact wide product, None on divisor zero/overflow).
//!
//! 2. **Verbatim-copy differential tests**: `NetworkFeeTracker::take_fee` and
//!    `DcaState` live inside the `pallet-cf-swapping` crate (too heavy to
//!    depend on directly), so byte-identical copies of those items are
//!    embedded here (module `pallet_copy`) and differential-tested against
//!    plain-Rust transcriptions of the verified Verus ports (module
//!    `verified_model`). A drift-check test asserts, at test time, that the
//!    copies still appear verbatim in the pallet source file, so the copies
//!    cannot silently diverge from the shipped code.
//!
//! 3. **Property replays**: the key theorems proven in Verus (fee splitting,
//!    chunking fairness, DCA conservation, no-dust) are re-checked as
//!    executable properties against the pallet copies.

/// Byte-identical copies of items from
/// state-chain/pallets/cf-swapping/src/lib.rs (see the drift-check tests at
/// the bottom of this file).
pub mod pallet_copy {
    use sp_arithmetic::traits::{Saturating, Zero};
    use sp_arithmetic::Permill;
    use std::collections::BTreeSet;

    pub type AssetAmount = u128;
    pub type SwapId = u64;
    pub const SWAP_DELAY_BLOCKS: u32 = 2;

    /// `log_or_panic!` panics under test (mirrors cf-runtime-utilities with
    /// debug assertions enabled).
    macro_rules! log_or_panic {
        ($($arg:tt)*) => {
            panic!($($arg)*)
        };
    }

    pub struct DcaParameters {
        pub number_of_chunks: u32,
        pub chunk_interval: u32,
    }

    pub struct FeeRateAndMinimum {
        pub rate: Permill,
        pub minimum: AssetAmount,
    }

    pub struct FeeTaken {
        pub remaining_amount: AssetAmount,
        pub fee: AssetAmount,
    }

    pub struct NetworkFeeTracker {
        pub network_fee: FeeRateAndMinimum,
        pub accumulated_stable_amount: AssetAmount,
        pub accumulated_fee: AssetAmount,
    }

    impl NetworkFeeTracker {
        pub const fn new(network_fee: FeeRateAndMinimum) -> Self {
            Self { network_fee, accumulated_stable_amount: 0, accumulated_fee: 0 }
        }

        // --- begin verbatim copy: NetworkFeeTracker::take_fee ---
	pub fn take_fee(&mut self, stable_amount: AssetAmount) -> FeeTaken {
		if stable_amount.is_zero() {
			return FeeTaken { remaining_amount: 0, fee: 0 };
		}
		let calculated_fee = core::cmp::max(
			self.network_fee.rate * (self.accumulated_stable_amount.saturating_add(stable_amount)),
			self.network_fee.minimum,
		);
		let fee_taken =
			core::cmp::min(calculated_fee.saturating_sub(self.accumulated_fee), stable_amount);

		self.accumulated_fee.saturating_accrue(fee_taken);
		self.accumulated_stable_amount.saturating_accrue(stable_amount);

		FeeTaken { remaining_amount: stable_amount.saturating_sub(fee_taken), fee: fee_taken }
	}
        // --- end verbatim copy ---
    }

    pub struct DcaState {
        pub scheduled_chunks: BTreeSet<SwapId>,
        pub remaining_input_amount: AssetAmount,
        pub remaining_chunks: u32,
        pub chunk_interval: u32,
        pub accumulated_output_amount: AssetAmount,
    }

    impl DcaState {
        // --- begin verbatim copy: DcaState methods ---
	fn new(input_amount: AssetAmount, params: Option<DcaParameters>) -> DcaState {
		DcaState {
			remaining_input_amount: input_amount,
			remaining_chunks: params.as_ref().map(|p| p.number_of_chunks).unwrap_or(1),
			// Chunk interval won't be used for non-DCA swaps but seems nicer to
			// set a reasonable default than unwrap Option when it is needed:
			chunk_interval: params.as_ref().map(|p| p.chunk_interval).unwrap_or(SWAP_DELAY_BLOCKS),
			accumulated_output_amount: 0,
			scheduled_chunks: BTreeSet::new(),
		}
	}

	/// Calculate the amount of the next chunk to be scheduled.
	fn calculate_next_chunk(&self) -> Option<AssetAmount> {
		if self.remaining_chunks > 0 {
			let chunk_input_amount = self
				.remaining_input_amount
				.checked_div(self.remaining_chunks as u128)
				.unwrap_or(0);

			Some(chunk_input_amount)
		} else {
			None
		}
	}

	/// Called directly after a chunk has been scheduled. Records the new swap in the DCA state.
	fn record_scheduled_chunk(
		&mut self,
		scheduled_chunk_swap_id: SwapId,
		scheduled_chunk_amount: AssetAmount,
	) {
		// Add the new chunk to the scheduled swaps.
		self.scheduled_chunks.insert(scheduled_chunk_swap_id);

		// Update the remaining values
		self.remaining_chunks.saturating_reduce(1);
		self.remaining_input_amount.saturating_reduce(scheduled_chunk_amount);
	}

	/// Remove the completed chunk from the DCA state and accumulate the output amount.
	fn record_chunk_completion(
		&mut self,
		completed_chunk_swap_id: SwapId,
		completed_chunk_output_amount: AssetAmount,
	) {
		if self.scheduled_chunks.remove(&completed_chunk_swap_id) {
			self.accumulated_output_amount += completed_chunk_output_amount;
		} else {
			log_or_panic!(
				"Invariant violation: the completed swap id {completed_chunk_swap_id} does not match a scheduled chunk."
			);
		}
	}
        // --- end verbatim copy ---

        pub fn new_pub(input_amount: AssetAmount, params: Option<DcaParameters>) -> DcaState {
            Self::new(input_amount, params)
        }

        pub fn calculate_next_chunk_pub(&self) -> Option<AssetAmount> {
            self.calculate_next_chunk()
        }

        pub fn record_scheduled_chunk_pub(&mut self, id: SwapId, amount: AssetAmount) {
            self.record_scheduled_chunk(id, amount)
        }

        pub fn record_chunk_completion_pub(&mut self, id: SwapId, output: AssetAmount) {
            self.record_chunk_completion(id, output)
        }
    }
}

/// Plain-Rust transcriptions of the *verified* exec code in
/// formal-verification/verus/src/ (spec/proof clauses stripped, logic
/// byte-comparable by inspection). These are the "other side" of the
/// differential tests: Verus proved these algorithms correct; the tests below
/// show the pallet copies compute the same results.
pub mod verified_model {
    pub const MILLION: u128 = 1_000_000;
    pub const HALF_ADJ: u128 = 499_999;

    /// Transcription of verus/src/network_fee.rs::mul_ppm
    /// (Permill's `Rounding::NearestPrefDown` semantics).
    pub fn mul_ppm(x: u128, ppm: u32) -> u128 {
        let q = x / MILLION;
        let rem = x % MILLION;
        let high = q * (ppm as u128);
        let low = (rem * (ppm as u128) + HALF_ADJ) / MILLION;
        high + low
    }

    /// Transcription of verus/src/network_fee.rs::sat_add.
    fn sat_add(a: u128, b: u128) -> u128 {
        if a <= u128::MAX - b { a + b } else { u128::MAX }
    }

    /// Transcription of verus/src/network_fee.rs::sat_sub.
    fn sat_sub(a: u128, b: u128) -> u128 {
        if a >= b { a - b } else { 0 }
    }

    pub struct NetworkFeeTracker {
        pub rate_ppm: u32,
        pub minimum: u128,
        pub accumulated_stable_amount: u128,
        pub accumulated_fee: u128,
    }

    impl NetworkFeeTracker {
        pub fn new(rate_ppm: u32, minimum: u128) -> Self {
            Self { rate_ppm, minimum, accumulated_stable_amount: 0, accumulated_fee: 0 }
        }

        /// Transcription of verus/src/network_fee.rs::take_fee.
        pub fn take_fee(&mut self, stable_amount: u128) -> (u128, u128) {
            if stable_amount == 0 {
                return (0, 0);
            }
            let new_total = sat_add(self.accumulated_stable_amount, stable_amount);
            let rated = mul_ppm(new_total, self.rate_ppm);
            let calculated_fee = if rated >= self.minimum { rated } else { self.minimum };
            let fee_taken = {
                let due = sat_sub(calculated_fee, self.accumulated_fee);
                if due <= stable_amount { due } else { stable_amount }
            };
            self.accumulated_fee = sat_add(self.accumulated_fee, fee_taken);
            self.accumulated_stable_amount = sat_add(self.accumulated_stable_amount, stable_amount);
            (stable_amount - fee_taken, fee_taken)
        }
    }

    /// Transcription of verus/src/dca.rs::DcaState (ghost fields dropped).
    pub struct DcaState {
        pub scheduled_chunks: Vec<u64>,
        pub remaining_input_amount: u128,
        pub remaining_chunks: u32,
        pub chunk_interval: u32,
        pub accumulated_output_amount: u128,
    }

    impl DcaState {
        pub fn new(input_amount: u128, number_of_chunks: u32, chunk_interval: u32) -> Self {
            DcaState {
                scheduled_chunks: Vec::new(),
                remaining_input_amount: input_amount,
                remaining_chunks: number_of_chunks,
                chunk_interval,
                accumulated_output_amount: 0,
            }
        }

        pub fn calculate_next_chunk(&self) -> Option<u128> {
            if self.remaining_chunks > 0 {
                Some(self.remaining_input_amount / (self.remaining_chunks as u128))
            } else {
                None
            }
        }

        pub fn record_scheduled_chunk(&mut self, id: u64, amount: u128) {
            self.scheduled_chunks.push(id);
            self.remaining_chunks -= 1;
            self.remaining_input_amount -= amount;
        }

        pub fn record_chunk_completion(&mut self, id: u64, output: u128) {
            let i = self
                .scheduled_chunks
                .iter()
                .position(|x| *x == id)
                .expect("completed chunk must be scheduled");
            self.scheduled_chunks.remove(i);
            self.accumulated_output_amount += output;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use sp_arithmetic::Permill;
    use sp_core::{U256, U512};

    // ------------------------------------------------------------------
    // Drift checks: the verbatim copies must still exist, byte-for-byte,
    // in the pallet source. If the pallet code changes, these tests fail
    // and both the copies and the Verus ports must be re-audited.
    // ------------------------------------------------------------------
    const SWAPPING_SRC: &str =
        include_str!("../../../state-chain/pallets/cf-swapping/src/lib.rs");
    const THIS_SRC: &str = include_str!("lib.rs");

    fn extract_copy(marker: &str) -> String {
        let begin = format!("        // --- begin verbatim copy: {marker} ---\n");
        let end = "        // --- end verbatim copy ---";
        let start = THIS_SRC.find(&begin).expect("begin marker") + begin.len();
        let stop = THIS_SRC[start..].find(end).expect("end marker") + start;
        THIS_SRC[start..stop].to_string()
    }

    #[test]
    fn take_fee_copy_matches_pallet_source() {
        let copy = extract_copy("NetworkFeeTracker::take_fee");
        assert!(
            SWAPPING_SRC.contains(&copy),
            "cf-swapping's NetworkFeeTracker::take_fee has changed; re-audit \
             formal-verification/verus/src/network_fee.rs and update this copy"
        );
    }

    #[test]
    fn dca_state_copy_matches_pallet_source() {
        let copy = extract_copy("DcaState methods");
        assert!(
            SWAPPING_SRC.contains(&copy),
            "cf-swapping's DcaState has changed; re-audit \
             formal-verification/verus/src/dca.rs and update this copy"
        );
    }

    // ------------------------------------------------------------------
    // 1. Spec conformance: cf-amm-math mul_div vs the verified spec.
    // ------------------------------------------------------------------

    fn u256(lo: u128, hi: u128) -> U256 {
        (U256::from(hi) << 128) | U256::from(lo)
    }

    /// The specification proven of the Verus kernel, computed here in U512
    /// space: floor/ceil of the exact product, None iff c == 0 or the result
    /// exceeds U256::MAX.
    fn spec_mul_div(a: U256, b: U256, c: U256) -> (Option<U256>, Option<U256>) {
        if c.is_zero() {
            return (None, None);
        }
        let prod = a.full_mul(b); // exact U512 product
        let (q, r) = U512::div_mod(prod, U512::from(c));
        let floor: Option<U256> = q.try_into().ok();
        let ceil = if r.is_zero() {
            floor
        } else {
            floor.and_then(|f| f.checked_add(U256::one()))
        };
        (floor, ceil)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        #[test]
        fn amm_math_mul_div_matches_verified_spec(
            a_lo: u128, a_hi: u128, b_lo: u128, b_hi: u128, c_lo: u128, c_hi: u128,
            // Also exercise small/degenerate divisors heavily.
            small_c in 0u128..=4,
            use_small_c: bool,
        ) {
            let a = u256(a_lo, a_hi);
            let b = u256(b_lo, b_hi);
            let c = if use_small_c { U256::from(small_c) } else { u256(c_lo, c_hi) };

            let (spec_floor, spec_ceil) = spec_mul_div(a, b, c);
            prop_assert_eq!(cf_amm_math::mul_div_floor_checked(a, b, c), spec_floor);
            prop_assert_eq!(cf_amm_math::mul_div_ceil_checked(a, b, c), spec_ceil);
        }

        // ------------------------------------------------------------------
        // 2. Differential: pallet take_fee (verbatim copy, real Permill)
        //    vs the verified model.
        // ------------------------------------------------------------------

        #[test]
        fn take_fee_pallet_equals_verified_model(
            ppm in 0u32..=1_000_000,
            minimum in 0u128..=10_000_000_000_000u128,
            amounts in proptest::collection::vec(0u128..=1_000_000_000_000_000u128, 1..20),
        ) {
            let mut pallet = pallet_copy::NetworkFeeTracker::new(pallet_copy::FeeRateAndMinimum {
                rate: Permill::from_parts(ppm),
                minimum,
            });
            let mut model = verified_model::NetworkFeeTracker::new(ppm, minimum);

            for &amount in &amounts {
                let taken = pallet.take_fee(amount);
                let (model_remaining, model_fee) = model.take_fee(amount);

                prop_assert_eq!(taken.fee, model_fee);
                prop_assert_eq!(taken.remaining_amount, model_remaining);
                prop_assert_eq!(pallet.accumulated_fee, model.accumulated_fee);
                prop_assert_eq!(
                    pallet.accumulated_stable_amount,
                    model.accumulated_stable_amount
                );

                // Property replay of the Verus ensures clauses:
                prop_assert!(taken.fee <= amount);
                prop_assert_eq!(taken.remaining_amount + taken.fee, amount);
            }
        }

        // Chunking fairness: total fee over any chunking == lump-sum fee
        // (the invariant proven inductive in Verus, replayed on the pallet copy).
        #[test]
        fn take_fee_chunking_fairness(
            ppm in 0u32..=1_000_000,
            minimum in 0u128..=1_000_000u128,
            amounts in proptest::collection::vec(0u128..=1_000_000_000u128, 1..20),
        ) {
            let rate = Permill::from_parts(ppm);
            let mut chunked = pallet_copy::NetworkFeeTracker::new(pallet_copy::FeeRateAndMinimum {
                rate,
                minimum,
            });
            let mut total_fee = 0u128;
            for &amount in &amounts {
                total_fee += chunked.take_fee(amount).fee;
            }

            let total: u128 = amounts.iter().sum();
            let lump_sum = core::cmp::min(core::cmp::max(rate * total, minimum), total);
            prop_assert_eq!(total_fee, lump_sum);
        }

        // Permill multiplication behaves exactly like the verified mul_ppm.
        #[test]
        fn permill_mul_matches_verified_mul_ppm(x: u128, ppm in 0u32..=1_000_000) {
            prop_assert_eq!(Permill::from_parts(ppm) * x, verified_model::mul_ppm(x, ppm));
        }

        // ------------------------------------------------------------------
        // 3. Differential: pallet DcaState (verbatim copy) vs verified model,
        //    plus property replays (conservation, no dust).
        // ------------------------------------------------------------------

        #[test]
        fn dca_state_pallet_equals_verified_model(
            input in 0u128..=1_000_000_000u128,
            num_chunks in 1u32..=20,
            chunk_interval in 1u32..=10,
            outputs in proptest::collection::vec(0u128..=1_000_000u128, 20),
        ) {
            let mut pallet = pallet_copy::DcaState::new_pub(
                input,
                Some(pallet_copy::DcaParameters { number_of_chunks: num_chunks, chunk_interval }),
            );
            let mut model = verified_model::DcaState::new(input, num_chunks, chunk_interval);

            let mut next_id = 0u64;
            let mut scheduled_total = 0u128;
            let mut executed_input_total = 0u128;
            let mut in_flight: Vec<(u64, u128)> = Vec::new();

            // Schedule-then-complete, mirroring process_swap_outcome's loop.
            loop {
                let pallet_chunk = pallet.calculate_next_chunk_pub();
                let model_chunk = model.calculate_next_chunk();
                prop_assert_eq!(pallet_chunk, model_chunk);

                match pallet_chunk {
                    Some(amount) => {
                        // No-dust / bounds properties proven in Verus:
                        prop_assert!(amount <= pallet.remaining_input_amount);
                        if pallet.remaining_chunks == 1 {
                            prop_assert_eq!(amount, pallet.remaining_input_amount);
                        }

                        let id = next_id;
                        next_id += 1;
                        pallet.record_scheduled_chunk_pub(id, amount);
                        model.record_scheduled_chunk(id, amount);
                        in_flight.push((id, amount));
                        scheduled_total += amount;
                    },
                    None => {
                        // debug_assert mechanized in Verus:
                        prop_assert_eq!(pallet.remaining_input_amount, 0);
                        break;
                    },
                }

                // Complete the oldest in-flight chunk.
                let (id, amount) = in_flight.remove(0);
                let output = outputs[(id as usize) % outputs.len()];
                pallet.record_chunk_completion_pub(id, output);
                model.record_chunk_completion(id, output);
                executed_input_total += amount;

                prop_assert_eq!(
                    pallet.accumulated_output_amount,
                    model.accumulated_output_amount
                );

                // Conservation invariant proven in Verus:
                let in_flight_total: u128 = in_flight.iter().map(|(_, a)| a).sum();
                prop_assert_eq!(
                    input,
                    pallet.remaining_input_amount + in_flight_total + executed_input_total
                );
            }

            // All chunks scheduled exactly account for the input.
            prop_assert_eq!(scheduled_total, input);
            prop_assert_eq!(pallet.remaining_chunks, 0);
        }
    }

    /// Observation (documented in REPORT.md): with fewer input units than
    /// chunks, `calculate_next_chunk` returns Some(0) and the pallet
    /// schedules zero-amount swaps.
    #[test]
    fn zero_amount_chunks_are_scheduled() {
        let pallet = pallet_copy::DcaState::new_pub(
            2,
            Some(pallet_copy::DcaParameters { number_of_chunks: 3, chunk_interval: 1 }),
        );
        assert_eq!(pallet.calculate_next_chunk_pub(), Some(0));
    }
}

#[cfg(test)]
mod broker_probe;

#[cfg(test)]
mod boost_probe;
