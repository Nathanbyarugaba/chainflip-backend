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
│   ├── check.sh                 runs every config (incl. expected-failure
│   │                            "finding" configs) and the spec mutations
│   └── mutations.sh             anti-vacuity mutation testing
├── verus/               Verus-verified ports of state-chain arithmetic
│   ├── src/network_fee.rs       NetworkFeeTracker::take_fee
│   ├── src/dca.rs               DcaState chunk accounting
│   ├── src/mul_div.rs           mul_div floor/ceil kernel (256-bit)
│   ├── src/broker_fee.rs        take_broker_fees Permill split + overcharge witness
│   └── verify.sh                verifies the crate; rejects assume/admit
└── conformance/         Property tests binding models to shipped code
    └── src/lib.rs               spec-conformance + differential tests
```

## Running everything

```bash
# 1. Fetch the pinned tools (TLC needs Java; Verus installs its own rustc).
./tools/get-tools.sh

# 2. TLA+: all model checks, finding configs, and spec mutations (~1 min).
./tla/check.sh

# 3. Verus: machine-check all proofs (~5 s).
./verus/verify.sh

# 4. Conformance: differential/property tests against the real crates.
(cd conformance && cargo test)
```

Everything here is additive: no existing state-chain code is modified, and
the `verus/` and `conformance/` crates are intentionally *not* members of the
repository cargo workspace (Verus pins its own toolchain; conformance is a
test-only crate).
