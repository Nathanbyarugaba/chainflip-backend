# Formal verification — witnessing & egress integrity

Machine-checked models and proofs for Chainflip's highest-value theft surfaces:

1. **Witnessing / deposit crediting** — Byzantine threshold, witnesser idempotence, deposit replay, reorg/hash-binding, amount casting.
2. **Egress / broadcast** — payload immutability, at-most-once success, resign/replay safety, nonce discipline, failure-reporter binding.

These are **faithful models** of the Rust algorithms (not a verified compilation of the runtime). Each surface has a correspondence note under `correspondence/` and, where the model is a pure function, a Rust differential test that pins the live code to the formulas.

## Layout

```
formal-verification/
  fstar/          F* models (threshold arithmetic, amounts / BTC sum)
  lean/           Lean 4 + Mathlib models (witnesser, deposit, reorg, broadcast)
  correspondence/ Model ↔ Rust mapping tables and assumptions
  scripts/verify.sh
```

## Threat → theorem index

| Surface | Threat | Tool | Entry point |
|---|---|---|---|
| A | Threshold off-by-one / sub-threshold forge / stall | F* + Lean | `fstar/Chainflip.Threshold.fst`, `lean/Chainflip/Threshold.lean` |
| B | Witnesser double-credit / forged credit | Lean | `lean/Chainflip/Witnesser.lean` |
| C | Deposit replay (same tx credited twice) | Lean | `lean/Chainflip/DepositReplay.lean` |
| D | Reorg double-spend-into-credit / unbound height votes | Lean | `lean/Chainflip/Reorg.lean` |
| E | Amount truncation / BTC u64 wrap (CF-SEC-013) | F* | `fstar/Chainflip.Amounts.fst` |
| F | Double outflow / stale nonce / unbound failure reports (CF-SEC-006/007/023) | Lean | `lean/Chainflip/Broadcast.lean` |

Negative theorems that reproduce audit findings (and show the recommended fix restores the property) are marked in the correspondence docs.

## Toolchain

Pinned / tested with:

- **F\*** `v2026.07.24` (bundled Z3 4.13.3 / 4.15.3) — install via `curl -fsSL https://aka.ms/install-fstar | bash -s -- --release`
- **Lean 4** `v4.33.0-rc1` + Mathlib (see `lean/lean-toolchain`) — install via [elan](https://github.com/leanprover/elan)

## Verify

```bash
# All formal proofs
./formal-verification/scripts/verify.sh

# F* only
make -C formal-verification/fstar verify

# Lean only
( cd formal-verification/lean && lake update && lake build )

# Rust differential tests (threshold model)
cargo nextest run -p utilities threshold_matches_formal_model
```

CI for these proofs is **opt-in** (toolchains are large). Run `verify.sh` locally or in a dedicated job.

## What this does *not* cover

- Direct verification of Rust / Substrate runtime code (would need extraction frameworks such as hax/Aeneas/Verus).
- Multisig / FROST cryptography internals (see `frost-security-review.md` and the Kudelski report).
- Implementation of the audit remediations — the proofs characterize correct behaviour and reproduce bugs as counterexamples; code patches are a separate change.
