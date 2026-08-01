# Correspondence — Surface C: Deposit replay / identity

## Rust source

| Model | Rust |
|---|---|
| `DepositId` | Per-chain deposit identity. BTC: `Utxo` (`tx_id`+`vout`) as `DepositDetails`; `TransactionInId = Hash` (tx id). Solana: `(SolAddress, u64)`. EVM: `evm::DepositDetails`. |
| `Ledger.credit` idempotent | Ingress-egress boost map `BoostedVaultTransactions` keyed by `tx_id`; witnesser `CallHashExecuted` binds the full witnessed call (amount, channel, details). |
| Boost vs normal | `creditPath` — both paths share the same dedup set |

## Theorems (Lean `Chainflip/DepositReplay.lean`)

| Id | Property |
|---|---|
| C1 | `credit_idempotent` / `credit_idempotent_balance` |
| C2 | `distinct_ids_balance` |
| C3 | `boost_vs_normal_exclusive` |

## Assumptions / out of model

- Fee deduction / dust / zero post-fee boosted path (CF-SEC-009/010) are not modeled here.
- Engine-side observation correctness is assumed; this model covers state-chain credit idempotence only.
