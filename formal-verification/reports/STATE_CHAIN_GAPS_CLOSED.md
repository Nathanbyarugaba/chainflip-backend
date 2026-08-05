# Closing Previously Missed State-Chain Areas

**Question:** Can we formally verify the state-chain areas we skipped earlier?  
**Answer:** **Yes** — with the same targeted TLA+/Verus approach. This note
documents what was closed in this pass, what remains, and how to reproduce.

---

## 1. What was previously missed

From `REPORT.md` §2 / §7:

| Area | Status before | Status now |
|---|---|---|
| AMM swap loop / LP fee accounting | Out of scope | **Closed (abstract)** — `AmmSwapConservation.tla` + Verus fee-reduction bounds |
| Elections / ExactValue consensus | Out of scope | **Closed** — `ExactValueConsensus.tla` + Verus `success_threshold` uniqueness |
| Lending repay / liquidation conservation | Out of scope | **Closed** — `LendingRepay.tla` + interest coupling `LendingInterestRepay.tla` |
| Ingress/egress (beyond boost) | Partial (boost lifecycle done) | Still open for deposit-channel expiry / batching |
| Tick math (`SqrtPrice::from_tick`) | Stretch | **Closed** — `tick_math.rs` unwrap obligations |
| Trading strategies / governance / emissions | Out of scope | Still open |

---

## 2. New artifacts

```
formal-verification/tla/state_chain_gaps/
  AmmSwapConservation.tla|.cfg
  ExactValueConsensus.tla|.cfg
  LendingRepay.tla|.cfg
  check.sh

formal-verification/verus/src/thresholds.rs
```

```bash
./formal-verification/tla/state_chain_gaps/check.sh   # 3/3
./formal-verification/verus/verify.sh                 # 83 verified, 0 errors
```

---

## 3. Results

### 3.1 AMM swap conservation (`AmmSwapConservation.tla`)

Abstracts `inner_swap` + `reduce_by_pool_fee`: fee taken from input, remainder
sold into discrete liquidity lots, output from quote inventory.

| Config | Outcome | Distinct states |
|---|---|---|
| `AmmSwapConservation.cfg` | **pass** | 26 004 |

**Invariants:** `PoolReceivedEqualsConsumed`, `FeesBounded`, `StepsBounded`.

**Verus:** `theorem_reduce_by_pool_fee_bounds` — fee reduction never increases
input; identity at fee=0.

*Limitation:* constant-product lot fill is an abstraction of sqrt-price math;
conservation of *reserves under the model* is proved, not bit-exact tick
crossing.

### 3.2 ExactValue election consensus (`ExactValueConsensus.tla`)

Models `ExactValue::check_consensus` with
`success_threshold = floor((2n-1)/3)+1`.

| Config | Outcome | Distinct states |
|---|---|---|
| `ExactValueConsensus.cfg` (4 authorities, 2 values) | **pass** | 99 |

**Invariants:** `AtMostOneConsensusValue`, `ConsensusSound`, `UniqueConsensus`,
`AbstentionSafety`.

**Verus:** `theorem_at_most_one_value_reaches_success` — `2·success_threshold > n`.

No counterexample: with a correct 2/3-style threshold, two distinct values
cannot both reach consensus.

### 3.3 Lending repay conservation (`LendingRepay.tla`)

Models `repay_principal` and fee-taking `repay_via_liquidation` (interest
collection abstracted away).

| Config | Outcome | Distinct states |
|---|---|---|
| `LendingRepay.cfg` | **pass** | 1 493 |

**Invariants:** `Conservation` (`provided = repaid + fees + excess`),
`OwedNonIncreaseOnRepay`, `ExcessBounded`.

*Limitation:* `collect_pending_interest` before liquidation fee (which can
increase `owed`) is not modelled; a follow-up can refine that interaction.

---

## 4. Findings in this pass

No new **fund-loss** counterexamples in these three models. The invariants
held under exhaustive TLC for the stated bounds.

Remaining risk is outside the models (full tick AMM, interest→owed coupling,
ingress channel recycle beyond boost).

---

## 4b. Follow-up closures (this commit)

### Tick math (`verus/src/tick_math.rs`)

Mechanizes the two unwrap obligations in `SqrtPrice::from_tick`:

1. `theorem_checked_mul_no_overflow` / `theorem_u128_const_mul_safe` —
   `C: u128`, `r ≤ 2^128` ⇒ `C·r < 2^256`.
2. `theorem_r_nonzero_msb_bound` — `128 + Σ⌊log₂ Cᵢ⌋ − 19·128 = 38 ≥ 0`.

### Lending interest → repay coupling (`LendingInterestRepay.tla`)

| Config | Outcome | Distinct states |
|---|---|---|
| `LendingInterestRepay.cfg` | pass (conservation) | 19 772 |
| `LendingInterestFeeBase.cfg` | **expected fail** | fee-base grows after interest capitalisation |

**Observation (LEND-1):** `repay_via_liquidation` calls `collect_pending_interest()`
*before* computing `liquidation_fee = rate * min(provided, owed)`, so pending
interest increases the fee base. Conservation of `provided` still holds; the
borrower pays a larger fee than on pre-collect owed. Intentional but sharp.

## 5. Recommended next closures

1. **Tick math** — mechanize `SqrtPrice::from_tick` overflow comments in Verus.  
2. **Lending interest collection** — extend `LendingRepay` so
   `collect_pending_interest` can grow `owed` before fee/repay.  
3. **Ingress deposit-channel lifecycle** — expiry/recycle without boost.  
4. **MonotonicMedian / oracle_price** electoral systems — same pattern as ExactValue.

---

## 6. Verdict

**Yes — the missed high-value state-chain areas can be (and have begun to be)
formally verified.** This pass closes AMM conservation (abstract), ExactValue
consensus uniqueness, and lending repay conservation, with green TLC and Verus
proofs. Remaining gaps are listed above as concrete follow-ups.
