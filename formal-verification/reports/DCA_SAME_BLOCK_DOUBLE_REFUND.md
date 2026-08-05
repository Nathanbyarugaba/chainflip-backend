# Finding Report: DCA Same-Block Double-Refund Drops User Funds

| Field | Value |
|---|---|
| **ID** | FV-2026-DCA-001 (REPORT.md §6.2) |
| **Severity** | **High** — user fund loss |
| **Status** | Confirmed by TLC model check **and** pallet unit tests |
| **Component** | `pallet-cf-swapping` (`cf-swapping`) |
| **Trigger** | `chunk_interval == 1` DCA + FoK, with ≥2 same-request chunks failing the refund path in one `on_finalize` batch |

---

## 1. Executive summary

When two (or more) chunks of the **same** DCA swap request take the
fill-or-kill **refund** path inside a **single** `on_finalize` batch, the
protocol can permanently drop one chunk’s input:

- The first `refund_failed_swap` cannot cancel its sibling (already removed
  from `ScheduledSwaps` for the batch) → `log_or_panic!` / silent miss.
- It then deletes the `SwapRequest`.
- The second `refund_failed_swap` finds no request → early return; that
  chunk’s input is never refunded and never egressed.

**Proven loss in the release unit test:** exactly **one chunk** of input
(`INPUT_AMOUNT / number_of_chunks`) is unrecoverable.

This is **fund loss**, not theft to an attacker: value disappears from every
user-visible sink (refund egress + output egress).

---

## 2. Root cause (source)

### 2.1 Batch extraction removes all due swaps first

`on_finalize` (`lib.rs` ~1144–1190):

```rust
let swaps_to_execute = ScheduledSwaps::<T>::mutate(|swaps| {
    let (swaps_to_execute, remaining_swap_ids) =
        core::mem::take(swaps).into_iter().partition(|(_, swap)| {
            swap.execute_at <= current_block
        });
    *swaps = remaining_swap_ids;
    swaps_to_execute.into_values().collect::<Vec<_>>()
});
// ...
for (swap, reason) in failed_swaps {
    match swap.refund_params {
        Some(ref params)
            if BlockNumberFor::<T>::from(params.refund_block) <
                current_block + retry_delay =>
        {
            Self::refund_failed_swap(swap, reason);  // may run twice
        }
        _ => { Self::reschedule_swap(...); }
    }
}
```

All due swaps leave `ScheduledSwaps` **before** any refund runs.

### 2.2 First refund cannot see the sibling

`refund_failed_swap` (~2346–2388):

```rust
let canceled_swaps_amount = dca_state
    .scheduled_chunks
    .iter()
    .filter(|swap_id| *swap_id != &swap.swap_id)
    .fold(0, |acc, swap_id| {
        acc.saturating_add(Self::cancel_swap(
            *swap_id,
            SwapFailureReason::PredecessorSwapFailure,
        ))
    });
```

`cancel_swap` (~2492–2501):

```rust
let amount = swaps.remove(&swap_id).map(|swap| { ... swap.input_amount });
if amount.is_none() {
    log_or_panic!(
        "Attempted to cancel swap {swap_id}, but it was not found in ScheduledSwaps"
    );
}
amount.unwrap_or_default()  // → 0 when sibling already in this batch
```

### 2.3 Second refund is a no-op

```rust
let Some(mut request) = SwapRequests::<T>::take(swap_request_id) else {
    log_or_panic!("Swap request {swap_request_id} not found");
    return;  // chunk input dropped
};
```

---

## 3. Concrete numeric scenario (matches the unit test)

| Quantity | Value |
|---|---|
| `INPUT_AMOUNT` | 40 000 |
| `number_of_chunks` | 4 |
| `chunk_interval` | 1 |
| Chunk size | 10 000 |
| After chunk 1 succeeds | output egressed ≈ 19 980 (after broker fee × rate); `remaining_input` = 10 000; scheduled = {2, 3} |
| FoK | `retry_duration = 0`, min price unmet after rate crash |
| Same-batch refund of chunks 2 & 3 | |

**Accounting after the buggy batch:**

| Sink | Amount (input units) |
|---|---|
| Chunk 1 (swapped / credited as input) | 10 000 |
| Refund egress | 20 000 (= chunk2 + remaining) |
| **Lost (chunk 3)** | **10 000** |
| Total | 40 000 |

Invariant broken:

```text
INPUT = swapped_input + refunded_input + still_scheduled + remaining
      ≠  recovered   (missing one in-flight chunk)
```

---

## 4. Formal proof (TLA+ / TLC)

**Spec:** `formal-verification/tla/SwapDcaFok.tla`  
**Finding config:** `SwapDcaFokDoubleFailure.cfg` (`AllowSameBlockFailures = TRUE`)

```bash
cd formal-verification
./tools/get-tools.sh
java -cp tools/tla2tools.jar tlc2.TLC \
  -config tla/SwapDcaFokDoubleFailure.cfg tla/SwapDcaFok.tla
```

**Result:** `Error: Invariant InputConservation is violated.`

Counterexample transcript saved at:

`formal-verification/reports/tlc_dca_double_refund_counterexample.txt`

The model’s `DoubleFailureRefund` action encodes the same storage interaction
as the Rust batch (sibling not cancelable; second refund drops the request).

Mainline configs with `AllowSameBlockFailures = FALSE` keep
`InputConservation` (single-refund-at-a-time world).

---

## 5. Code proof (pallet unit tests)

### 5.1 Debug — invariant panic

```bash
cargo test -p pallet-cf-swapping --features proptest \
  proof_dca_same_block_double_refund_debug_panics -- --nocapture
```

**Observed:**

```text
log_or_panic: Attempted to cancel swap 3, but it was not found in ScheduledSwaps
test ...debug_panics - should panic ... ok
```

### 5.2 Release — numeric fund loss

```bash
cargo test -p pallet-cf-swapping --features proptest --release \
  proof_dca_same_block_double_refund_loses_funds -- --nocapture
```

**Observed:** `ok` — asserts:

- `refunded == 2 * CHUNK_AMOUNT` (20 000)
- `INPUT_AMOUNT - (CHUNK_AMOUNT + refunded) == CHUNK_AMOUNT` (**10 000 lost**)

Test location:

`state-chain/pallets/cf-swapping/src/tests/dca.rs`
→ `proof_dca_same_block_double_refund_loses_funds`
→ `proof_dca_same_block_double_refund_debug_panics`

### 5.3 How the test forces one batch

After chunk 1 succeeds, both remaining swaps are still outstanding but on
consecutive `execute_at` values. The test aligns both onto the next block
(and refreshes FoK `refund_block`) so a single `on_finalize` sees

```text
execute_at <= current_block
```

for both — the same predicate the production hook uses. That is exactly the
condition under which the bug’s storage assumptions break.

---

## 6. When this is reachable in production

Necessary ingredients:

1. **DCA with `chunk_interval == 1`** (two chunks kept in flight).
2. **≥2 chunks of that request due in one `on_finalize`**  
   (`execute_at <= now` for both), e.g. after catch-up / skipped blocks, or
   any scheduling alignment that lands them together.
3. **FoK refund path** for both in that batch  
   (`refund_block < now + retry_delay`), e.g. `retry_duration == 0` or
   retries exhausted onto a shared deadline.

`chunk_interval == 1` is a supported, tested configuration
(`dca_with_one_block_interval*`).

---

## 7. Suggested fix

Refund at **request** granularity inside the batch, not per-swap:

1. Group `failed_swaps` by `swap_request_id`.
2. For each request that should refund, sum input amounts of all its failed
   chunks **from the in-memory batch** (not via `cancel_swap` on
   `ScheduledSwaps`), plus `remaining_input_amount`, then refund once and
   delete the request once.
3. Alternatively: leave failed same-request siblings in a side structure
   until refund accounting finishes.

Also replace the `log_or_panic!` “unreachable” assumptions with handling that
preserves conservation even if the assumption fails.

---

## 8. Reproduction checklist

| Step | Command / artifact | Expected |
|---|---|---|
| TLC finding | `SwapDcaFokDoubleFailure.cfg` | `InputConservation` violated |
| Debug unit test | `proof_dca_same_block_double_refund_debug_panics` | panics: cancel swap not found |
| Release unit test | `proof_dca_same_block_double_refund_loses_funds` | loses exactly one chunk |
| Mainline TLC | `SwapDcaFok.cfg` (no same-block double failure) | conservation holds |

---

## 9. Verdict

**Confirmed user fund loss** in `pallet-cf-swapping` when multiple FoK refunds
for the same DCA request run in one `on_finalize` batch under
`chunk_interval == 1`. Evidence: TLC counterexample + release unit test
showing a **10 000**-unit hole on a **40 000**-unit request (one full chunk).
