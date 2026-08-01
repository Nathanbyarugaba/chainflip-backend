# Correspondence — Surface F: Egress / broadcast authorization

## Rust source (`state-chain/pallets/cf-broadcast/src/lib.rs`)

| Model | Rust |
|---|---|
| `Payload` / `Attempt` | API call + threshold-signed transaction (dest/amount fixed at construction) |
| `St.authorize` | `threshold_sign_and_broadcast` / `PendingBroadcasts` |
| `St.succeed` | `transaction_succeeded` → `egress_success` → `clean_up_broadcast_storage` (removes `TransactionOutIdToBroadcastId`) |
| `St.abort` | Abort path into `AbortedBroadcasts` |
| `St.resign refresh` | `re_sign_aborted_broadcasts` / `re_sign_broadcast` with `refresh_replay_protection` (CF-SEC-007; Solana no-op CF-SEC-023) |
| `St.reportFailure requireNominee` | `transaction_failed` / `handle_broadcast_failure` — currently any validator (CF-SEC-006); `requireNominee=true` models the fix |
| `St.maybeAbort` | Abort when enough distinct failure reporters accumulate |

## Theorems (Lean `Chainflip/Broadcast.lean`)

| Id | Property |
|---|---|
| F1 | `payload_immutable_{succeed,abort,resign}` |
| F2 | `succeed_idempotent_effect`, `succeed_effect_le_one_*` |
| F3 | Negative `resign_without_refresh_reuses_replay`; positive `resign_with_refresh_advances` / `resign_with_refresh_no_collision` |
| F4 | `authorize_nonce`, `refreshed_nonce_ne_original` |
| F5 | Negative `unbound_failure_accepts_stranger`; positive `nominee_bound_rejects_stranger`, `single_stranger_cannot_abort` |

## Assumptions / out of model

- On-chain "same (nonce, replay) ⇒ both txs valid if either lands" is an environment assumption about EVM nonces / Solana durable nonces.
- Broadcast barrier / nomination scheduling details are abstracted.
- Does not verify threshold-signature cryptography itself.
