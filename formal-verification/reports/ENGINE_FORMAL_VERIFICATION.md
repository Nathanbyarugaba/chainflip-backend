# Formal Verification Report: Chainflip Engine

**Methods:** TLA+ / TLC (exhaustive model checking) and Verus (machine-checked
proofs), targeting `engine/` (multisig client + RPC retrier helpers).

**Toolchain:** same pinned TLC / Verus as `formal-verification/tools/get-tools.sh`.

---

## 1. Executive summary

The engine’s safety-critical control paths around **multisig ceremony broadcast
stages**, **broadcast verification / blame**, and the **RPC retrier** were
modelled in TLA+ and checked with TLC. Supporting helpers
(`threshold_for_broadcast_verification`, `max_sleep_duration`) were proved in
Verus.

**Suite:** `tla/engine/check.sh` → **5/5**; Verus crate → **74 verified, 0 errors**.

Two engine-side findings (counterexamples) were produced:

| ID | Finding | Severity |
|---|---|---|
| ENG-1 | `verify_broadcasts` returns **empty blame** on `InsufficientVerificationMessages` | Medium (accountability / slashing gap) |
| ENG-2 | `RetryLimit::Limit(0)` still **runs attempt 0** | Low (API footgun) |

No fund-theft path was found in the modelled engine surface; ceremony crypto
correctness and P2P authenticity remain out of scope (trusted).

---

## 2. Scope and trust model

### Covered

| Artifact | Source | Level |
|---|---|---|
| `tla/engine/CeremonyBroadcast.tla` | `multisig/.../broadcast.rs`, `ceremony_runner.rs` | design |
| `tla/engine/BroadcastVerification.tla` | `multisig/.../broadcast_verification.rs` | design |
| `tla/engine/Retrier.tla` | `engine/src/retrier.rs` | design |
| `verus/src/engine_helpers.rs` | `utils.rs` threshold; `retrier.rs` sleep cap | code |

### Not covered

- Full keygen / signing stage machines (DKG / TSS crypto)
- P2P networking, serialization compatibility beyond existing unit tests
- Per-chain witness pipelines (BTC/EVM/Sol/…) and election voting
- State-chain observer extrinsic submission
- Cryptographic hardness assumptions

---

## 3. Results

### 3.1 Ceremony broadcast stage (`CeremonyBroadcast.tla`)

Models `BroadcastStage` collect → Ready / timeout → finalize, with Own always
inserting a local message on init.

| Config | Outcome | Distinct states |
|---|---|---|
| `CeremonyBroadcast.cfg` (3 parties, 2 stages, quorum 2) | pass | 21 |

**Invariants:** `OwnAlwaysPresent`, `NeverReportOwnForAbsence`,
`SuccessImpliesAllStages`, `ReportedWereAbsent`.

### 3.2 Broadcast verification (`BroadcastVerification.tla`)

Models `verify_broadcasts` with `threshold = n/2` and majority `count > threshold`.

| Config | Outcome | Distinct states |
|---|---|---|
| `BroadcastVerification.cfg` (n=3) | pass | 314 928 |
| `BroadcastVerificationFinding.cfg` (n=2) | **expected fail** | ENG-1 |

**Invariants (mainline):** `OkImpliesAllAgreed`,
`InsufficientVerifBlamesNobody` (documents Rust behaviour),
`ConsistentQuorumSucceeds`.

### 3.3 Retrier (`Retrier.tla`)

| Config | Outcome | Distinct states |
|---|---|---|
| `Retrier.cfg` (Limit=3, FailForever) | pass | 8 |
| `RetrierLimitZero.cfg` | **expected fail** | ENG-2 |

**Invariants:** `AtMostOneDelivery`, `AttemptIndexValid`.

### 3.4 Verus (`engine_helpers.rs`)

Proved: threshold examples (1→0, 2→1, 3→1, …); quorum bounds;
`max_sleep_duration` never exceeds cap; Limit(0) allows attempt 0.

---

## 4. Findings

### ENG-1 — Empty blame on insufficient verification messages

**Source:** `engine/multisig/src/client/common/broadcast_verification.rs` ~131–135:

```rust
if verification_messages.len() <= threshold {
    // TODO: consider reporting the parties that didn't send ...
    return Err((BTreeSet::new(), BroadcastFailureReason::InsufficientVerificationMessages))
}
```

**TLC:** `BroadcastVerificationFinding.cfg` violates
`BlameSomeoneOnInsufficientVerif` — states exist with
`outcome = FailInsufficientVerif` and nonempty `submitters` but
`reported = {}`.

**Impact:** When too few parties send verification messages (including the
n=2 case where a single message is ≤ threshold), **no one is reported**.
Honest nodes cannot attribute blame; a silent / lazy / targeted-dropping
adversary is not slashed via this path. The in-source TODO acknowledges this.

**Suggested fix:** Report parties in `participating_idxs` absent from
`verification_messages` (and/or below-quota broadcasters), with care for
symmetric reporting as noted in the TODO.

### ENG-2 — `RetryLimit::Limit(0)` still performs attempt 0

**Source:** `engine/src/retrier.rs` ~448–500 — the `next_attempt >= max_attempts`
check runs only on the **retry** path after a failure delay. Attempt 0 is
always started from the receive path.

**TLC:** `RetrierLimitZero.cfg` violates `AttemptNeverStarts`.

**Impact:** Callers passing `0` as a limit still incur one RPC attempt.
Documented as “maximum attempts” in `request_with_limit`; `Limit(0)` is a
footgun (behaves like “1 try then fail” after the first error), not a
silent no-op.

**Suggested fix:** Reject `Limit(0)` at the API, or treat `max_attempts == 0`
as immediate `DoneErr` without submission.

---

## 5. How to reproduce

```bash
cd formal-verification
./tools/get-tools.sh
./tla/engine/check.sh          # 5/5
./verus/verify.sh              # 74 verified, 0 errors
```

---

## 6. Verdict

Engine ceremony broadcast collection and retrier attempt accounting are
**safe under the modelled invariants**, with two accountability / API
findings (ENG-1, ENG-2) backed by TLC counterexamples. Cryptographic stage
logic and witnessing pipelines remain future work.
