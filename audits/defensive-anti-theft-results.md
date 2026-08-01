# Defensive anti-theft sandbox results — 2026-08-01

## Scope & method

**Not exploit testing.** Per project security policy this work does **not** include
exploit PoCs, attack payloads, or instructions for stealing funds.

Instead we added **defensive** pallet tests that attempt theft-relevant *state
transitions* under the mock runtimes and assert they are **rejected** or that
effects fire at most once. Where a known audit gap meant the secure property
failed, we **fixed** the gap and locked it with a passing test.

Surfaces covered: witnessing / deposit-credit forgery & double-credit;
broadcast abort abuse & double outflow.

## Results summary

| Check | Surface | Result | Notes |
|---|---|---|---|
| Sub-threshold coalition cannot dispatch | Witnesser | **PASS** | 1 of 3 votes < success(3)=2; no `CallHashExecuted` |
| Threshold dispatch idempotent | Witnesser | **PASS** | Third vote does not re-dispatch |
| Duplicate vote cannot inflate quorum | Witnesser | **PASS** | `DuplicateWitness` |
| Non-nominee cannot report failure | Broadcast | **PASS** (after fix) | CF-SEC-006 remediated |
| Nominee can still report failure | Broadcast | **PASS** | Liveness preserved |
| `transaction_succeeded` at most once | Broadcast | **PASS** | Second call → `InvalidPayload` |
| Aborted-then-succeeded single cleanup | Broadcast | **PASS** | Late success cleans once; no second success |

## Fix applied

### CF-SEC-006 — unbound broadcast failure reports

**Before:** `transaction_failed` accepted any validator origin and appended them
to `FailedBroadcasters`, allowing a non-nominee coalition to force abort/retry.

**After:** The extrinsic requires the reporter to equal
`AwaitingBroadcast.nominee` for that attempt. Timeouts still attribute failure
to the nominee via `on_initialize` → `handle_broadcast_failure` (unchanged).

New error: `Error::NotNominatedBroadcaster`.

## How to re-run

```bash
cargo test -p pallet-cf-witnesser defensive_anti_theft
cargo test -p pallet-cf-broadcast defensive_anti_theft
cargo test -p pallet-cf-broadcast   # full suite (46 tests)
```

## Still open (not covered by this defensive suite)

These remain as modeled/documented risks from the formal-verification work and
the July 2026 critical review — **not** demonstrated via exploit PoCs here:

- CF-SEC-007 / CF-SEC-023 — resign without replay refresh / Solana refresh no-op
- CF-SEC-013 — BTC unchecked `u64` output sum
- CF-SEC-017 / CF-SEC-018 — height-only / unbound hash elections
- End-to-end deposit amount / decimal confusion across engine parsers

Recommended next step: same style of **defensive** unit tests + targeted fixes
for the items above (fail-closed assertions, no attacker tooling).
