# Correspondence — Surface D: Reorg safety / hash binding

## Rust / engine source

| Model | Code / audit |
|---|---|
| `safeHeight = tip - confirmationDepth` | Chain-tracking + confirmation depth configuration; monotonic-median electoral systems in `cf-elections` |
| Height-only votes | `EngineElectionType::BlockHeight { submit_hash: false }` — CF-SEC-017 |
| Hash-bound votes | `ByHash(hash)` election mode — CF-SEC-018 flags missing hash re-check |

## Theorems (Lean `Chainflip/Reorg.lean`)

| Id | Property |
|---|---|
| D1 | `preserved_prefix_bound`, `safe_credit_survives_reorg` — credit-safe heights lie strictly below any reorg of depth `< confirmationDepth` |
| D2 | `height_only_ambiguous` (negative), `hash_bound_unique` (positive) |

## Assumptions / out of model

- Models the *arithmetic* of confirmation depth; does not re-implement the full election state machine.
- Negative theorem D2 justifies requiring hash-bound votes for deposit witnessing (audit recommendation).
