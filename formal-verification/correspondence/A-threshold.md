# Correspondence — Surface A: Byzantine threshold arithmetic

## Rust source

| Model definition | Rust |
|---|---|
| `threshold n` | `cf_utilities::threshold_from_share_count` in `utilities/src/lib.rs` |
| `success n` | `cf_utilities::success_threshold_from_share_count` |
| `failure n` | `cf_utilities::failure_threshold_from_share_count` |
| Test vectors | `check_threshold_calculation` unit test (same file) |

## Call sites (consumers of the formulas)

- `state-chain/pallets/cf-witnesser/src/lib.rs` — dispatch when `num_votes == success_threshold_from_share_count(num_authorities)`
- `state-chain/pallets/cf-threshold-signature/src/response_status.rs` — `super_majority_threshold`
- Elections / signer nomination (same helper)

## Theorems

| Id | Property | F* | Lean |
|---|---|---|---|
| A1 | Test vectors match Rust unit test | `test_vectors` | `test_vectors` |
| A2 | `success = threshold+1`, `failure = n-threshold` | `succ_eq`, `fail_eq` | same |
| A3 | Success is a strict majority (`n/2 < success ≤ n`) | `succ_bounds` | `succ_bounds` |
| A4 | Sub-threshold coalition cannot forge (`b ≤ threshold ⇒ b < success`) | `forge_resistance` | same |
| A5 | No-stall: `h ≥ success ↔ b ≤ failure-1` | `no_stall`, `fail_minus_one_eq` | same |
| A6 | Quorum intersection nonempty | `quorum_overlap_positive` | same |
| A7 | Equality dispatch is not an off-by-one on first crossing | `first_crossing` | same |

## Differential test

`utilities` crate: `threshold_matches_formal_model` — exhaustive `n ∈ 0..=1000`.

## Assumptions / out of model

- The authority set size `n` is the count used by `EpochInfo::authority_count_at_epoch`.
- Cryptographic soundness of threshold signatures given ≥ `success` honest signers is assumed (see Kudelski / frost-security-review).
