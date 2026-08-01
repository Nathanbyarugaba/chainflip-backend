# Correspondence — Surface E: Amount casting / BTC output sum

## Rust source

| Model | Rust |
|---|---|
| `widen` / `narrow` | `Chain::ChainAmount: Into<AssetAmount> + TryFrom<AssetAmount>` in `state-chain/chains/src/lib.rs` (`AssetAmount = u128`) |
| `pow10` / `rescale` | Per-asset `decimals()` in `state-chain/primitives/src/chains/assets.rs` (pricing / display scale) |
| `wrapping_add_u64` | `state-chain/chains/src/btc/api.rs` — `total_output_amount += transfer_param.amount` (CF-SEC-013) |
| `checked_add_u64` / `checked_sum` | Recommended fix for CF-SEC-013 |

## Theorems (F* `Chainflip.Amounts.fst`)

| Id | Property |
|---|---|
| E1 | `widen_narrow_roundtrip` |
| E2 | `narrow_no_truncation`, `narrow_fails_closed` |
| E3 | `rescale_same_decimals`, `rescale_scale_up_injective` |
| E4 | `checked_add_sound`, `checked_sum_correct`; negative `wrapping_can_disagree` |

## Assumptions / out of model

- State-chain vault accounting uses `AssetAmount` (u128); per-chain native widths differ (BTC u64, etc.).
- Decimal rescale here documents pricing-scale identity; silent theft via wrong decimals would require a cast site that truncates — E2 forbids that pattern.
