# Formal Verification of the Chainflip State Chain

This directory contains formal verification artifacts for the state chain:
TLA+ specifications of its critical distributed state machines (model-checked
exhaustively with TLC) and Verus machine-checked proofs of its critical
financial arithmetic, plus a conformance suite binding the verified models to
the shipped code.

**Read [REPORT.md](REPORT.md) for the scope, trust model, results, and
findings.**

## Layout

```
formal-verification/
├── REPORT.md            The verification report (start here)
├── tools/get-tools.sh   Downloads the pinned toolchain (TLC 1.7.4, Verus
│                        0.2026.08.02); binaries are gitignored
├── tla/                 TLA+ specs + TLC configs
│   ├── AuthorityRotation.tla    authority/key rotation state machine
│   ├── BroadcastLifecycle.tla   broadcast pallet lifecycle
│   ├── SwapDcaFok.tla           DCA / fill-or-kill swap execution
│   ├── BrokerFeeSplit.tla       take_broker_fees rounding / fund safety
│   ├── BoostLifecycle.tla        deposit boost / finalise / loss / mismatch
│   ├── engine/                  engine/ (multisig + retrier) models
│   ├── state_chain_gaps/         AMM / elections / lending (gap closure)
│   │   ├── CeremonyBroadcast.tla
│   │   ├── BroadcastVerification.tla
│   │   ├── Retrier.tla
│   │   └── check.sh
│   ├── check.sh                 runs every config (incl. expected-failure
│   │                            "finding" configs) and the spec mutations
│   └── mutations.sh             anti-vacuity mutation testing
├── verus/               Verus-verified ports (state-chain + engine helpers)
│   ├── src/network_fee.rs       NetworkFeeTracker::take_fee
│   ├── src/dca.rs               DcaState chunk accounting
│   ├── src/mul_div.rs           mul_div floor/ceil kernel (256-bit)
│   ├── src/broker_fee.rs        take_broker_fees Permill split + overcharge witness
│   ├── src/boost_fee.rs         boost fee attribution conservation
│   ├── src/engine_helpers.rs    broadcast threshold + retrier sleep cap
│   └── verify.sh                verifies the crate; rejects assume/admit
├── reports/             Dedicated finding reports
│   ├── DCA_SAME_BLOCK_DOUBLE_REFUND.md
│   ├── ENGINE_FORMAL_VERIFICATION.md
│   └── STATE_CHAIN_GAPS_CLOSED.md
└── conformance/         Property tests binding models to shipped code
    └── src/lib.rs               spec-conformance + differential tests
```

## Running everything

```bash
# 1. Fetch the pinned tools (TLC needs Java; Verus installs its own rustc).
./tools/get-tools.sh

# 2. TLA+ (state-chain models + mutations).
./tla/check.sh

# 3. TLA+ (engine/ multisig + retrier models).
./tla/engine/check.sh

# 3b. TLA+ (previously missed state-chain areas).
./tla/state_chain_gaps/check.sh

# 4. Verus: machine-check all proofs (~5 s).
./verus/verify.sh

# 5. Conformance: differential/property tests against the real crates.
(cd conformance && cargo test)
```

Engine report: [`reports/ENGINE_FORMAL_VERIFICATION.md`](reports/ENGINE_FORMAL_VERIFICATION.md).

Everything here is additive: no existing state-chain code is modified, and
the `verus/` and `conformance/` crates are intentionally *not* members of the
repository cargo workspace (Verus pins its own toolchain; conformance is a
test-only crate).
