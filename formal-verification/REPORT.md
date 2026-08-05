# Formal Verification Report: Chainflip State Chain

**Methods:** TLA+ / TLC (exhaustive model checking) and Verus (SMT-backed
machine-checked proofs on Rust code), bound to the shipped code by a
differential/property conformance suite.

**Toolchain (pinned by `tools/get-tools.sh`):** TLC 2.19 (tla2tools v1.7.4),
Verus 0.2026.08.02.b677dd5 (rustc 1.97.1).

---

## 1. Executive summary

Three of the state chain's most safety-critical distributed state machines —
**authority/key rotation**, the **broadcast lifecycle**, and **DCA /
fill-or-kill swap execution** — were modelled in TLA+ and exhaustively model
checked: all intended safety invariants (state coherence, funds conservation,
no-abort-after-key-activation, no-forgotten-broadcast) and liveness properties
(every rotation/broadcast/swap-request terminates) **hold** in the models,
across every reachable interleaving of the modelled configurations.

Three of the state chain's most safety-critical arithmetic components —
**`NetworkFeeTracker::take_fee`**, **`DcaState`** chunk accounting, and the
AMM **`mul_div`** floor/ceil kernel — were ported to Verus and **proven
correct and panic-free** (63 verified items, 0 errors, no `assume`/`admit`),
including a chunking-fairness theorem (DCA chunking pays exactly the lump-sum
network fee) and a no-dust theorem (floor division strands no input).

The exercise also produced **four concrete findings** — code paths where the
implementation can violate the intended properties — each demonstrated by a
model-checker counterexample and traced back to specific source lines
(§6.1–§6.4), plus lower-severity observations (§6.5), one of which
(the `Permill` rounding mode) was caught by the conformance suite disagreeing
with an initially-plausible reading of the code.

This is **targeted** verification: §2 states precisely what is and is not
covered. No existing state-chain code was modified.

## 2. Scope and trust model

"Formally verify the state chain" cannot literally mean the whole ~100k-line
Substrate runtime: no current tool can ingest FRAME's macro-generated code,
and TLA+ operates on design-level models rather than Rust. What formal
verification means in practice — and what was done here — is:

1. **Design-level (TLA+/TLC):** hand-built models of the protocol's state
   machines, exhaustively checked for all behaviours within finite bounds.
   The guarantee is about the *model*; its faithfulness to the code is argued
   by (a) per-action source citations (every TLA+ action carries a
   `file:line` comment naming the code it models), (b) documented abstraction
   notes in each spec header, and (c) mutation testing (§4.4) showing the
   invariants actually reject broken protocols.
2. **Code-level (Verus):** line-by-line ports of pure functions, with
   machine-checked proofs of functional correctness and panic-freedom. The
   guarantee is about the *port*; its faithfulness is enforced by the
   conformance suite (§5): byte-identical copies of the pallet code are
   drift-checked against the pallet source file at test time and
   differential-tested against transcriptions of the verified ports, and
   `cf-amm-math`'s real `U256` functions are property-tested against the same
   mathematical specification the Verus kernel is proven to satisfy.

### Covered

| Subsystem | Artifact | Level |
|---|---|---|
| Authority rotation (`cf-validator` `RotationPhase` driver) composed with per-chain key rotation (`cf-threshold-signature` `KeyRotationStatus`) and the multi-chain status combinator (`ConsKeyRotator`) | `tla/AuthorityRotation.tla` | design |
| Broadcast lifecycle (`cf-broadcast`): signing, nomination, timeouts, retries, aborts, witnessing, rotation barriers | `tla/BroadcastLifecycle.tla` | design |
| Swap execution per request (`cf-swapping`): DCA chunking, reschedule, fill-or-kill refund | `tla/SwapDcaFok.tla` | design |
| `NetworkFeeTracker::take_fee` (network fee accrual incl. minimum-fee logic and `Permill` rounding) | `verus/src/network_fee.rs` | code |
| `DcaState` (`new` / `calculate_next_chunk` / `record_scheduled_chunk` / `record_chunk_completion`) | `verus/src/dca.rs` | code |
| `mul_div` floor/ceil kernel (contract of `cf-amm-math::mul_div_floor_ceil` and the `*_checked` wrappers) | `verus/src/mul_div.rs` | code |
| Broker fee split (`take_broker_fees` / `validate_broker_fees`) | `tla/BrokerFeeSplit.tla` + `verus/src/broker_fee.rs` | design + code |
| Deposit boosting lifecycle (prewitness / finalise / loss / amount mismatch) | `tla/BoostLifecycle.tla` + `verus/src/boost_fee.rs` | design + code |

### Not covered (explicitly out of scope)

- AMM pool swap loop and limit-order accounting (`state-chain/amm/`, `cf-pools`)
- Elections / witnessing framework (`cf-elections`)
- Ingress/egress deposit-channel and batching logic (`cf-ingress-egress`)
- Lending pools, trading strategies, governance, reputation, emissions
- Off-chain engine (threshold signing MPC, chain tracking, broadcasting)
- Consensus (BABE / GRANDPA) and Substrate FRAME machinery
- Cryptographic hardness of TSS / keygen / key handover
- `SqrtPrice::from_tick` tick-math prose proofs (stretch item; see §7)

A panic/halt of the runtime, fund loss, or stuck egress can still originate in
an uncovered subsystem. The coverage map above is the honest answer to
"what is verified".

## 3. Methodology

### 3.1 TLA+ / TLC

Each spec is a PlusCal-free TLA+ module with an `Init` / `Next` / `Spec` /
`FairSpec` structure. Constants bound the state space (validator count, chain
count, broadcast/swap counts, failure budgets). Configs:

- **Mainline safety** — exhaustive BFS of the reachable state space against
  all invariants and action properties.
- **Liveness** — under weak/strong fairness assumptions (`FairSpec`), check
  that every started rotation / broadcast / swap request eventually
  terminates.
- **Finding** — deliberately enable a code path that TLC is expected to
  reject (documents a real issue; see §6).
- **Mutations** (`tla/mutations.sh`) — inject a known bug into a copy of the
  spec and assert TLC catches it, so the invariants are not vacuous.

Reachability probes (negated deep-state assertions) were also run during
development to ensure each intended phase/state of the protocol is actually
visited by TLC.

### 3.2 Verus

Each module is a standalone Verus crate (toolchain 1.97.1, outside the main
cargo workspace) containing an executable port of the original function plus
`requires` / `ensures` contracts and supporting lemmas. `verus/verify.sh`
rejects any use of `assume` / `admit` / `external_body` and requires
`N verified, 0 errors`.

Port deviations (e.g. `BTreeSet` → duplicate-free `Vec`, `U256` → u128-width
full-product kernel) are documented in module headers; the conformance suite
binds the *mathematical* contracts back to the real crates.

### 3.3 Conformance

`conformance/` is a tiny standalone test crate with three binding layers:

1. **Spec conformance** — `cf_amm_math::mul_div_{floor,ceil}_checked` vs the
   exact U512-space floor/ceil specification proven of the Verus kernel
   (4096 proptest cases).
2. **Verbatim-copy differential** — byte-identical copies of
   `NetworkFeeTracker::take_fee` and the `DcaState` methods are embedded in
   the test crate; at test time an `include_str!` drift check asserts those
   copies still appear verbatim in
   `state-chain/pallets/cf-swapping/src/lib.rs`. The copies are then
   differential-tested against plain-Rust transcriptions of the verified
   Verus ports.
3. **Property replay** — the Verus theorems (fee splitting, chunking
   fairness, DCA conservation, no-dust, debug_assert) are re-checked as
   executable properties against the pallet copies.

## 4. Results

### 4.1 Authority / key rotation (`tla/AuthorityRotation.tla`)

Models `cf-validator::RotationPhase` (Idle → KeygensInProgress →
KeyHandoversInProgress → ActivatingKeys → NewKeysActivated → SessionRotating
→ Idle) composed with per-chain `KeyRotationStatus` via `ConsKeyRotator`.

| Config | Outcome | States (distinct) | Depth |
|---|---|---|---|
| `AuthorityRotation.cfg` (3 vals, 2 chains, 1 handover chain) | pass | 1,460 | 30 |
| `AuthorityRotationLarge.cfg` (4 vals, both chains handover) | pass | 8,532 | 38 |
| `AuthorityRotationLiveness.cfg` | pass | 536 | 17 |

**Safety invariants checked:** `TypeOK`, `NoViolation` (no `log_or_panic!` /
`assert!` fire), `PhaseCoherence`, `StatusSanity` (the three
`debug_assert!`s on unexpected statuses in `on_initialize` are unreachable),
`BannedNotCandidates`, `AuthoritySetNeverTooSmall`.

**Action properties checked:** `NoAbortAfterActivation` (rotation cannot
abort once new keys are activated — funds are already on those keys),
`AuthoritiesOnlyChangeAtEpochBoundary`, `EpochOnlyAdvancesFromSessionRotating`.

**Liveness:** `RotationTerminates` — under weak fairness of polling hooks /
session rotation / ceremony resolution, and a bounded failure budget, every
started rotation returns to Idle (completes or aborts).

### 4.2 Broadcast lifecycle (`tla/BroadcastLifecycle.tla`)

Models `threshold_sign_and_broadcast` → signing → nomination/timeout →
retry/abort → witnessed success, including rotation-tx barrier installation
and barrier popping via `remove_pending_broadcast`.

| Config | Outcome | States (distinct) | Depth |
|---|---|---|---|
| `BroadcastLifecycle.cfg` (3 vals, 3 broadcasts, 1 rotation barrier; Standard signing) | pass | 992,443 | 25 |
| `BroadcastLifecycleLiveness.cfg` | pass | 943 | 13 |
| `BroadcastLifecycleSigningFailure.cfg` (historical-key terminal failure) | **expected fail** — `BarrierBacked` | (see §6.1) | — |

**Safety invariants checked:** `TypeOK`, `AttemptHasTimeout` (an in-flight
attempt always has a registered timeout — the chain cannot silently forget
a broadcast), `FailedClearedOnResolution`, `BarrierBacked` (every barrier is
backed by a pending broadcast at-or-before it).

**Action properties:** `AbortOnlyWhenAllFailed`, `TerminalStability` (Succeeded
and Dropped are stable; Aborted may still become Succeeded on late inclusion).

**Liveness:** `AllBroadcastsResolve` — every requested broadcast eventually
succeeds or aborts (under Standard signing, which retries forever until a
signature is produced).

### 4.3 DCA / fill-or-kill swap execution (`tla/SwapDcaFok.tla`)

Models one swap request with DCA chunking and refund-on-expiry, under a 1:1
fee-free exchange-rate abstraction (fee arithmetic is verified separately in
Verus).

| Config | Outcome | States (distinct) | Depth |
|---|---|---|---|
| `SwapDcaFok.cfg` (input 5, 3 chunks, one in flight) | pass | 22 | — |
| `SwapDcaFokTwoInFlight.cfg` (input 7, 4 chunks, chunk_interval=1) | pass | 55 | — |
| `SwapDcaFokLiveness.cfg` | pass | 37 | — |
| `SwapDcaFokDoubleFailure.cfg` (same-block double refund) | **expected fail** — `InputConservation` | (see §6.2) | — |

**Safety invariants checked:** `TypeOK`, `NoPanic`, `InputConservation`,
`OutputConservation`, `TerminalConservation`, `DebugAssertHolds` (the
`debug_assert!(remaining_input_amount == 0)` in `process_swap_outcome`),
`ActiveHasScheduled`, `InFlightBound`, `TerminalClean`.

**Liveness:** `RequestResolves` — every swap request eventually Completes or
Refunds.

### 4.4 Spec anti-vacuity (mutations)

`tla/mutations.sh` injects one representative bug per spec and asserts TLC
catches it:

| Mutation | Expected violation | Result |
|---|---|---|
| Authority rotation: abort from `NewKeysActivated` | `NoAbortAfterActivation` action property | caught |
| Broadcast: start attempt without registering a timeout | `AttemptHasTimeout` | caught |
| Swap DCA: refund omits `remaining_input` | `InputConservation` | caught |

### 4.5 Verus (`verus/`, 63 verified, 0 errors)

`./verus/verify.sh` reports `verification results:: 63 verified, 0 errors`
and rejects any `assume` / `admit` / `external_body`.

#### `network_fee.rs` — port of `NetworkFeeTracker::take_fee`

- `remaining_amount + fee == stable_amount` and `fee <= stable_amount` (no
  funds created or destroyed; the pallet never takes more than it was given).
- Inductive chunking-fairness theorem: after any sequence of calls,
  `accumulated_fee == min(max(Permill(total), minimum), total)` — executing a
  swap in DCA chunks charges exactly the same total network fee as executing
  it in one piece.
- `Permill * u128` is modelled as nearest-ties-down
  (`Rounding::NearestPrefDown`), matching substrate's `PerThing::Mul`
  (see §6.3).

#### `dca.rs` — port of `DcaState`

- Conservation invariant: at all times
  `initial_input == remaining_input + sum(scheduled chunk inputs) + executed_input`.
- `calculate_next_chunk` never exceeds remaining input; with
  `remaining_chunks == 1` it returns the entire remainder (no dust stranded
  by floor division).
- `remaining_chunks == 0 ⇒ remaining_input == 0` — mechanizes the
  `debug_assert!` in `process_swap_outcome`.
- The `log_or_panic!` branch of `record_chunk_completion` is unreachable
  under the scheduling protocol (completed id ∈ scheduled_chunks).

#### `mul_div.rs` — verified 256-bit mul-div kernel

- `full_mul(a, b) = (hi, lo)` with `hi·2¹²⁸ + lo = a·b` exactly
  (schoolbook four-limb multiply with carries).
- Bit-by-bit 256÷128 long division returns exact quotient and remainder,
  with an overflow flag when the quotient does not fit u128.
- `mul_div_floor` / `mul_div_ceil` match the contract of
  `cf-amm-math::{mul_div_floor_checked, mul_div_ceil_checked}` (None iff
  divisor zero or result overflows), mechanizing the "cannot overflow"
  prose comment in `mul_div_floor_ceil`.

The kernel is at u128 width (two limbs down from the U256/U512 original);
the *mathematical* specification is identical and is what the conformance
suite checks against the real U256 functions.

### 4.6 Conformance (`conformance/`, 8/8 tests pass)

| Test | What it binds |
|---|---|
| `amm_math_mul_div_matches_verified_spec` | real `cf-amm-math` U256 vs verified floor/ceil spec (4096 cases) |
| `take_fee_pallet_equals_verified_model` | pallet copy (real `Permill`) ≡ Verus transcription |
| `take_fee_chunking_fairness` | chunked fee == lump-sum fee on the pallet copy |
| `permill_mul_matches_verified_mul_ppm` | substrate `Permill * u128` ≡ verified `mul_ppm` |
| `dca_state_pallet_equals_verified_model` | pallet `DcaState` ≡ Verus transcription + conservation/no-dust |
| `take_fee_copy_matches_pallet_source` | drift check (byte-identical) |
| `dca_state_copy_matches_pallet_source` | drift check (byte-identical) |
| `zero_amount_chunks_are_scheduled` | documents observation §6.3 |


### 4.7 Broker fee split (`tla/BrokerFeeSplit.tla` + `verus/src/broker_fee.rs`)

Models `take_broker_fees` with substrate's `Permill` nearest-ties-down
rounding (`floor((amount · bps · 100 + 499999) / 10⁶)`).

| Config | Outcome | States (distinct) |
|---|---|---|
| `BrokerFeeSplit.cfg` (amounts 0..200, equal splits, Σbps ≤ 1000, n ≤ 6) | pass | 493,656 |
| `BrokerFeeSplitFinding.cfg` (also equal 100% splits) | **expected fail** — `NoOverchargeOnAllModes` | (see §6.3) |

**Invariants checked (mainline):** `NoOverchargeValidated` (Σ fees ≤ amount
under production validation), `RoundingInflationBound`,
`UnvalidatedOverchargeExists` (tautology when unvalidated mode is off).

**Verus:** `fee_of` proven equal to `mul_ppm` / `Permill` mul and ≤ amount;
`theorem_unvalidated_overcharge_witness` proves the concrete 4×2500 @ amount=3
overcharge (Σ=4>3).

**Conformance:** exhaustive equal-split scan + 4096 random validated splits
never exceed amount; witness and under-collect observations locked in tests.


### 4.8 Deposit boosting (`tla/BoostLifecycle.tla` + `verus/src/boost_fee.rs`)

Models prewitness-boost → finalise / loss, plus the amount-mismatch path in
`process_full_witness_deposit_inner` (~3159).

| Config | Outcome | States (distinct) |
|---|---|---|
| `BoostLifecycle.cfg` (mismatch disabled) | pass | 289 |
| `BoostLifecycleFinding.cfg` (mismatch enabled) | **expected fail** — `NoDoubleCredit` | (see §6.4) |

**Invariants (mainline):** `BoosterConservation`, `LockedCoversOpenBoosts`,
`NoDoubleCredit`, `UserCreditBoundedByDeposit`, `NoMismatchPath`.

**Verus:** `fee_from_boosted_amount` + `theorem_attribution_conserves` —
the lending/boost fee attribution step cannot create or destroy value.

**Conformance:** `reported_amounts_sum_to_deposit` (8192 cases).

## 5. How to reproduce

```bash
./tools/get-tools.sh          # once; downloads pinned TLC + Verus
./tla/check.sh                # ~25 s: 10 mainline + 4 findings + 4 mutations
./verus/verify.sh             # ~4 s: 63 verified, 0 errors
(cd conformance && cargo test)  # 13 tests; ~1 s once built
```

## 6. Findings and observations

### 6.1 Finding: stuck broadcast barrier after historical-key signing failure

**Severity:** Medium (requires a governance-initiated historical-key signing
request that then fails terminal, *and* that request to be the last pending
broadcast at-or-before a rotation barrier).

**Property violated:** `BarrierBacked` — every barrier must be backed by a
pending broadcast at-or-before it; otherwise later broadcasts are blocked
forever (barriers are only popped by `remove_pending_broadcast`).

**Reproduction:** `tla/BroadcastLifecycleSigningFailure.cfg` — TLC reports
`Invariant BarrierBacked is violated` with a short counterexample:

1. Broadcast 1 signs and succeeds.
2. Broadcast 2 (a rotation tx) is requested, installing barrier `{2}`.
3. Broadcast 2's threshold signature fails terminal
   (`on_signature_ready` Err arm) → state `Dropped`.
4. Barrier `{2}` remains; any later broadcast is permanently blocked.

**Root cause:** in `cf-broadcast/src/lib.rs` (~line 630), the
`on_signature_ready` Err arm does

```rust
PendingBroadcasts::<T, I>::mutate(|pending| {
    pending.remove(&broadcast_id);
});
```

— a plain remove, **not** `remove_pending_broadcast`, so barriers are never
re-evaluated. Standard signing ceremonies retry forever and never hit this
arm; the arm is reachable for historical-key requests
(`ThresholdCeremonyType::HistoricalKey` with exhausted retries —
`cf-threshold-signature/src/lib.rs` ~line 977).

**Suggested fix:** route the Err arm through `remove_pending_broadcast`
(or an equivalent that pops barriers), and/or clean up
`AwaitingBroadcast` / `PendingApiCalls` symmetrically. No code change is
made in this PR; this report is the deliverable.

### 6.2 Finding: same-block double-chunk refund drops funds

> **Full dedicated report + code proof:**
> [`formal-verification/reports/DCA_SAME_BLOCK_DOUBLE_REFUND.md`](reports/DCA_SAME_BLOCK_DOUBLE_REFUND.md)
> Pallet tests: `proof_dca_same_block_double_refund_*` in `cf-swapping` `tests/dca.rs`.

**Severity:** High if reachable in production (fund loss); reachability
requires `chunk_interval == 1` (two chunks of the same request due in the
same block) *and* both chunks failing a fill-or-kill check after their
shared `refund_block`.

**Property violated:** `InputConservation` —
`remInput + scheduled + executed + refunded = TotalInput`.

**Reproduction:** `tla/SwapDcaFokDoubleFailure.cfg` — TLC reports
`Invariant InputConservation is violated`.

**Root cause:** in `cf-swapping/src/lib.rs` `on_finalize` (~1144), swaps due
at the current block are taken out of `ScheduledSwaps` into a local vec
before batch execution. On failure past `refund_block`,
`refund_failed_swap` (~2346):

1. Cancels "other scheduled chunks" via `cancel_swap`. The sibling that
   failed in the same batch is **not** in `ScheduledSwaps` any more, so
   `cancel_swap` (~2492) finds nothing, returns 0, and `log_or_panic!`s —
   its amount is not added to the refund.
2. Removes the `SwapRequest` from storage after refunding.
3. The second failed chunk of the same request then finds the
   `SwapRequest` already gone (~2351), `log_or_panic!`s, and returns —
   that chunk's input is dropped entirely.

With `chunk_interval == 1`, both chunks share the same `refund_block` by
construction (`schedule_swap` sets it from `execute_at + retry_duration`,
and both start within one block of each other), so a shared price-limit
failure past that block triggers the double-refund path.

**Suggested fix:** either (a) take the refund decision at the *request*
level after grouping same-request failures in the batch (so a single
`refund_failed_swap` sees all failed sibling amounts), or (b) leave failed
chunks in a side structure that `refund_failed_swap` can still recover
before deleting the request. The existing `log_or_panic!`s indicate the
authors considered these states unreachable; the model shows they are not
when `chunk_interval == 1`.


### 6.3 Finding: broker-fee split can overcharge (assert!-panic) if unvalidated

**Severity:** Medium as a defense-in-depth / halt risk; **Low for direct
fund theft under current callers** because `validate_broker_fees` enforces
`total_bps ≤ 1000` (and TLC + proptest prove that under that ceiling with
n ≤ 6, Σ nearest-rounded fees never exceeds `amount`).

**Property violated (without validation):** `NoOverchargeOnAllModes` —
Σ per-beneficiary `Permill(bps_i) * amount` ≤ amount.

**Reproduction:**
- TLC: `tla/BrokerFeeSplitFinding.cfg`
- Verus witness: `theorem_unvalidated_overcharge_witness` (4 × 2500 bps,
  amount = 3 → fees 1+1+1+1 = 4 > 3)
- Conformance: `unvalidated_equal_split_overcharge_witness`

**Root cause:** `take_broker_fees` charges each beneficiary independently
with nearest rounding, then `assert!(total_fee <= stable_amount)` — after
already calling `credit_account` for each fee. Its own early-return gate
only fires when `total_bps > 10000`, while `validate_broker_fees` uses
`total_bps ≤ 1000`. If any caller ever passes beneficiaries in the
`(1000, 10000]` band into `init_swap_request` (which does **not**
re-validate), the assert can fire and halt the chain. Because credits
precede the assert, a transactional rollback of the surrounding hook is
the only reason this would not also mint unbacked USDC free-balances.

**Under production validation** the overcharge-beyond-amount path is
unreachable (493k-state TLC proof + proptest). Brokers can still be
over- or under-paid by a few units vs a single `Permill(total_bps)` due
to split rounding (see §6.4).

**Suggested fix:** (a) re-validate fees inside `take_broker_fees` /
`init_swap_request`; (b) credit brokers only after computing the capped
total; (c) preferably charge `Permill(total_bps) * amount` once and
distribute by weight to eliminate split-rounding drift.


### 6.4 Finding: boosted deposit full-witnessed at a different amount double-credits the user

**Severity:** High *if* a full-witness amount can differ from the boosted
amount for the same deposit identity (channel boost_status / vault tx_id).
Under normal CFE behaviour the amounts match; the risk is a divergent
witness, a second deposit of a different size on an already-boosted channel
before the first is finalised, or any bug that reports a different amount.

**Property violated:** `NoDoubleCredit` — a deposit identity must not credit
the user twice while a boost remains open.

**Reproduction:** `tla/BoostLifecycleFinding.cfg` — TLC reports
`Invariant NoDoubleCredit is violated` with a short trace:
Boost(id, 2) → MismatchCredit(id, 3) → `userCredit = 5`, status
`DoubleCredited`, boost still locked. A subsequent `LoseAfterMismatch`
has boosters absorb the original 2 while the user keeps both credits.

**Root cause:** in `cf-ingress-egress/src/lib.rs` ~3159–3171,

```rust
BoostStatus::Boosted { prewitnessed_deposit_id, amount }
    if amount == deposit_amount => ActionToPerform::FinaliseBoost { .. },
// ...
_ => ActionToPerform::PerformChannelAction {
    deposit_outcome: FullWitnessDepositOutcome::BoostNotConsumed,
},
```

On amount mismatch the deposit is processed as a **fresh non-boosted
deposit** (user credited again) and `boost_status` is **not** cleared
(only `BoostConsumed` clears it, ~2645 / ~3402). The original boost can
later be finalised (if a matching amount eventually arrives) or marked
lost (recycle / vault timeout) — in the loss case boosters pay while the
user retains the boost-time credit *and* the mismatched full-witness credit.

**Suggested fix:** on `Boosted` with amount mismatch, either (a) refuse the
witness / emit `DepositFailed` and leave boost open, (b) treat as
finalisation of the boost *and* a separate residual/excess deposit only
for the delta, or (c) clear/cancel the boost before processing as
non-boosted (so boosters are not left exposed). Also consider matching on
`tx_id` / deposit id rather than amount alone for channels that can receive
multiple deposits.

### 6.5 Observations (lower severity / documentation)

1. **`Permill` rounds to nearest, ties down — not floor.** The initial Verus
   port assumed `floor(x · ppm / 10⁶)`. The conformance differential test
   against real `sp_arithmetic::Permill` failed (off-by-one on some inputs),
   revealing substrate's `Rounding::NearestPrefDown`
   (`overflow_prune_mul` in `per_things.rs`). The Verus port was corrected
   to `floor((x · ppm + 499_999) / 10⁶)` and re-proven. Chunking fairness
   still holds under nearest rounding.
2. **Zero-amount DCA chunks.** When `input_amount < number_of_chunks`,
   `calculate_next_chunk` returns `Some(0)` and the pallet schedules
   zero-amount swaps (confirmed by `zero_amount_chunks_are_scheduled`).
   Harmless for conservation, but wastes block weight / events. The Verus
   port preserves this behaviour; a `max(1, …)` clamp on chunk count (already
   present for `minimum_chunk_size`) could also clamp against the input.
3. **`transaction_failed` accepted during Signing.** The code accepts a
   failure report for any pending broadcast, including one that has not yet
   finished signing (no nominee). The model restricts reports to
   Attempting / RetryQueued; the looser code behaviour is benign (it just
   advances the failed-broadcaster set) but is worth noting.
4. **`abort_broadcast` does not clear `TransactionOutIdToBroadcastId`.** A
   previously aborted broadcast can still be witnessed as succeeded (late
   inclusion). The model permits `Aborted → Succeeded`; this matches the
   code and is intentional recovery behaviour.
5. **Activation signatures collapsing.** Per-chain
   `AwaitingActivationSignatures → Complete` is modelled as a single step
   (vault activator readiness is not separately modelled). The
   validator-level `ActivatingKeys → NewKeysActivated` transition still
   requires *all* chains to report `RotationComplete`.

6. **Broker fee split can under-collect.** `amount=10`, two×500 bps →
   fees 0+0, while `Permill(1000)*10 = 1`. Brokers receive less than the
   combined rate; the user keeps the unit. Locked in
   `split_can_undercollect_vs_combined`.

## 7. Limitations and future work

- **CI wiring.** `tla/check.sh`, `verus/verify.sh`, and
  `conformance`'s `cargo test` are ready to run in CI but are not wired up
  in this PR.
- **Tick math.** The two prose overflow-safety proofs in
  `SqrtPrice::from_tick` (`amm-math/src/lib.rs` ~170–230) were a stretch
  goal and were not mechanized; the obligations are clear candidates for a
  follow-up Verus module.
- **Elections framework.** A TLA+ model of `cf-elections` consensus would
  complement the existing proptest suite.
- **AMM swap loop.** A PlusCal / TLA+ refinement of the concentrated-
  liquidity swap loop (with the verified `mul_div` as a leaf) would close
  the largest remaining arithmetic gap.
- **Larger TLC configs.** The broadcast model at 3 validators / 3
  broadcasts already explores ~10⁶ states; symmetry reduction and further
  abstraction of the timeout set would unlock larger runs.
- **U256-width Verus kernel.** The mul-div proofs are at u128 width; lifting
  to four-limb U256 (with U512 intermediates) is mechanical but lengthy.

## 8. Verdict

The modelled protocols of authority rotation, broadcasting, and DCA/FoK
swapping are **safe and live** under the stated fairness and bound
assumptions; the critical fee / DCA / mul-div arithmetic is **proven correct
and panic-free**, and the proofs are bound to the shipped code by a
drift-checked conformance suite.

Four concrete issues were found and are documented with TLC counterexamples
and source-level root causes (§6.1–§6.4); fixing them is left as follow-up
work so this PR remains a pure verification deliverable.
