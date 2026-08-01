# Correspondence — Surface B: Witnesser dedup / idempotence

## Rust source

| Model | Rust (`state-chain/pallets/cf-witnesser/src/lib.rs`) |
|---|---|
| `St.votes` | `Votes` bitmask (one bit per authority index) |
| Duplicate vote → noop | `Error::DuplicateWitness` when bit already set |
| Dispatch condition | `num_votes == success_threshold_from_share_count(num_authorities)` and no prior `CallHashExecuted` in `[last_expired, current]` |
| `St.executed` | `CallHashExecuted` storage |
| `forceWitness` | `force_witness` extrinsic (governance; documented as replayable) |

## Theorems (Lean `Chainflip/Witnesser.lean`)

| Id | Property |
|---|---|
| B1 | `step_duplicate_noop`, `votes_card_le` |
| B2 | `no_redispatch_after_executed`, `dispatch_sets_executed`, `no_double_dispatch_consecutive` |
| B3 | `dispatch_implies_quorum`, `dispatch_has_honest` (uses Surface A) |
| B4 | `force_witness_replayable` (negative) |

## Assumptions / out of model

- Models a single `(call_hash, epoch)` vote set. Cross-epoch window check is abstracted as the `executed` flag.
- Call-hash collision resistance (blake2_256) is assumed.
- Safe-mode deferral (`WitnessedCallsScheduledForDispatch`) is out of model.
