# Fund-Theft Threat Model & Critical Vulnerability Review — 2026-07-29

Scope: the Chainflip State Chain (`state-chain/`) and shared chain-abstraction crate
(`state-chain/chains/`), reviewed for **fund-theft** vulnerabilities — i.e. any way an
adversary can take custody of, redirect, or mint value they are not entitled to.

This is a source-only review (no PoC execution). Findings are supported by concrete file
and line references and are labelled by confidence. Where a claim from the prior report
(`audits/critical-vulnerability-review-2026-07-24.md`) was checked against the code, the
result is recorded in the "Triage of prior findings" section — several of the earlier
"Critical, pending validation" items are downgraded here with evidence.

Reviewed at commit `99a8bc238` (main).

---

## 1. Methodology

The protocol was decomposed along the path that value actually travels:

```
external chain deposit ─▶ witnessing / elections ─▶ crediting (ingress-egress)
      ─▶ swap / AMM (swapping + pools) ─▶ egress scheduling ─▶ threshold signing
      ─▶ broadcast ─▶ external chain payout
```

Each hop was audited for the three ways funds get stolen:

1. **Redirection** — funds that should go to A are sent to the attacker instead
   (destination/refund/output-address manipulation).
2. **Inflation / minting** — the attacker causes the chain to believe it owes more than it
   does (fake deposits, double-credit, AMM output inflation, share dilution).
3. **Authorization bypass** — an unprivileged actor invokes a privileged fund-moving path
   (unsigned/origin confusion, forged threshold signatures, replay).

The following pallets/modules were mapped in depth: `cf-ingress-egress`, `cf-swapping`,
`cf-pools` + `amm`, `cf-broadcast`, `cf-threshold-signature`, `cf-funding` + `cf-flip`,
`cf-lending-pools`, and the address/CCM machinery in `state-chain/chains/src/address.rs`,
`ccm_checker.rs`, and the `btc`/`evm`/`sol`/`arb` sub-modules.

---

## 2. Threat model

### 2.1 Assets at risk

| Asset | Custody | Theft would look like |
|-------|---------|-----------------------|
| Vault balances on external chains (BTC UTXOs, EVM/Arb/BSC vault contracts, Solana vault PDAs) | Aggregate key (TSS) | An egress transfer to an attacker address |
| In-flight swap principal (deposited, not yet egressed) | State Chain accounting | Redirected output/refund address |
| LP liquidity in the AMM (`cf-pools`) | State Chain accounting | Withdrawing more than one's position; draining reserves |
| LP/lender balances (`AssetBalances`, lending pools) | State Chain accounting | Over-withdrawal / share dilution |
| Staked FLIP (`cf-funding` / `cf-flip`) | Ethereum StateChainGateway + SC accounting | Redemption for more than owed, or to a foreign address |
| Broker/affiliate/network fees | State Chain accounting | Fee-recipient substitution |

### 2.2 Actors and capabilities

| Actor | On-chain capability relevant to funds |
|-------|----------------------------------------|
| **Anonymous user / depositor** | Send funds to a deposit address; submit vault swaps on external chains |
| **Broker** (registered, signed) | Open swap deposit channels; set destination/refund/fee params for *their* channels; withdraw *their* fees |
| **LP** (registered, signed) | Provide/withdraw liquidity; place limit/range orders; provide/withdraw lending funds |
| **Single validator** | Submit witness votes; participate in signing/keygen ceremonies; report broadcast success/failure |
| **Supermajority of validators (authority set)** | Reach witness/election consensus; produce a valid threshold signature |
| **Governance** (`EnsureGovernance`) | Config changes; historical-key recovery broadcasts; safe-mode toggles |
| **Compromised external RPC** | Feed a validator's engine false chain data |

### 2.3 Trust boundaries (ranked by blast radius)

1. **Witnessing / elections consensus** (`cf-elections`, `cf-witnesser`, runtime election
   hooks). This is the *root of truth* for "a deposit happened", "a redemption was paid",
   "a broadcast succeeded", and "the external chain fee/base-fee is X". The on-chain pallets
   trust the witnessed value almost unconditionally.
2. **Threshold signature (TSS) key shares.** A quorum of key-share holders can sign any
   payload the chain *asks* it to sign.
3. **Governance.** Can invoke recovery paths that move funds outside the normal flow.
4. **Brokers**, for the specific channels their users choose to use (destination/refund
   addresses are broker-supplied for deposit-channel swaps).

### 2.4 Fund-theft attack tree (summary)

```
Steal funds
├── Redirect an egress/refund to attacker
│   ├── Change a scheduled destination via extrinsic ......... BLOCKED (destinations frozen at request creation)
│   ├── Malicious threshold payload swap in-flight ........... BLOCKED (payload bound + re-verified at dispatch)
│   ├── Broker sets attacker destination on their channel .... TRUST (user chooses broker) — §4.4
│   └── Solana CCM fallback to attacker on own deposit ....... SELF-DIRECTED, not theft of others — §4.3 / F-4
├── Mint / inflate a credit
│   ├── Double-credit a single deposit ...................... DEPENDS on election idempotency — §4.1 / F-1
│   ├── Forge a deposit / redemption witness ................ REQUIRES witness supermajority — §4.1 / F-1
│   ├── Inflate AMM swap output ............................. BLOCKED (floor/ceil favours pool; transactional)
│   └── Dilute lending pool shares ......................... BLOCKED (invariant: shares sum to 1; capped)
├── Bypass authorization on a fund path
│   ├── Unsigned signature_success forgery ................. BLOCKED (re-verified in pre_dispatch) — §5 / prior CF-SEC-004
│   ├── Over-withdraw own LP/lender/funding balance ........ BLOCKED (debit-before-mint; balance/bond caps)
│   └── Governance recovery misuse ........................ TRUST (governance) — prior CF-SEC-007/008
└── Halt the chain to strand funds (DoS, not theft) ......... §4.5 / F-5, F-6
```

**Headline conclusion:** No purely on-chain, unprivileged extrinsic path was found that lets
an external attacker steal protocol funds or another user's funds. The genuine
**critical fund-theft surface is the consensus/trust layer** (witnessing supermajority, TSS
key-share collusion, governance) — as designed. The code-level issues that were confirmed
are DoS / stuck-funds / robustness problems, not direct theft primitives. This is documented
below so remediation effort is aimed correctly.

---

## 3. Defenses that correctly block common theft patterns (verified)

These are worth stating because they are what makes the "no direct theft" conclusion hold.

- **Egress destinations are immutable after request creation.** `schedule_egress`
  (`cf-ingress-egress/src/lib.rs:3744`) only ever sends to a destination that came from a
  swap output / refund param / rejection refund address. There is no signed
  "withdraw-to-arbitrary-address" extrinsic in the ingress-egress pallet; batching
  (`do_egress_scheduled_fetch_transfer`) cannot rewrite `to`.
- **The threshold payload binds destination + amount + replay nonce end-to-end.** For EVM,
  `threshold_signature_payload()` hashes the transfer args together with replay protection
  (`chains/src/evm/api.rs:263`). Gas fields that are *not* signed are refreshed via
  `refresh_unsigned_data` and explicitly documented as not affecting calldata
  (`chains/src/lib.rs:650`). A validator cannot swap the payout parameters mid-ceremony.
- **Swap output math rounds against the swapper.** `execute_group_of_swaps` pro-rates with
  `Rounding::Down` (`cf-swapping/src/lib.rs:2786`); pool swaps ceil the input and floor the
  output and run inside `#[transactional]` (`cf-pools/src/lib.rs:1102`), so a failed
  fill (e.g. `InsufficientLiquidity`) rolls back the pool mutation. Fill-or-kill / oracle
  checks also run inside the transactional boundary, so a rejected swap never commits pool
  depletion or fee credits.
- **LPs can only burn their own position.** Burns are keyed by `(lp, order_id)`
  (`cf-pools/src/lib.rs:1887`), and mints debit the LP's balance *before* accepting
  liquidity (`:1865`, `:1945`).
- **Redemptions are capped by balance, bond, and restrictions.** `Redemption::new`
  (`cf-funding/src/lib.rs:206`) enforces `debit_amount <= account_balance`,
  `remaining_balance >= bond`, and `>= remaining_restricted`; the Ethereum payout is
  threshold-signed over `(nodeID, amount, funder, expiry, executor)`.
- **Addresses are chain-tagged and validated per asset.**
  `decode_and_validate_address_for_asset` (`chains/src/address.rs:446`) rejects an address
  whose `chain()` does not match the asset's chain; `EncodedAddress` is a SCALE enum whose
  variant *is* the chain, so cross-chain decoding confusion is not possible.

---

## 4. Findings (fund-theft oriented)

Findings are labelled **CONFIRMED** (behaviour verified in source), **CONDITIONAL**
(real code, exploitability depends on config/consensus), or **BY-DESIGN TRUST**
(a documented trust assumption, flagged for awareness).

### F-1 — Deposit crediting has no pallet-level replay/idempotency; correctness rests entirely on the election layer — **CONFIRMED (trust-critical)**

- Area: `cf-ingress-egress` witness → credit path; `cf-elections`.
- Impact class: value minting if the election-layer dedup is ever bypassed.

The full-witness deposit path (`process_channel_deposit_full_witness_inner`,
`cf-ingress-egress/src/lib.rs:2597` → `process_full_witness_deposit_inner`, `:3001`) takes
the deposit **amount and asset directly from the witness payload** (`DepositWitness`,
`:498`) and credits/initiates the swap with no on-chain check against a per-transaction
id. There is no `(tx_id, vout)` seen-set in this pallet; a second successful
`EnsureWitnessed` submission for the same deposit would credit twice. The dead
`AssetMismatch` error confirms the asset is trusted as-witnessed rather than checked
against the channel's asset.

This is the single largest fund-theft surface in the system and it is **by design** — the
elections/witnesser framework is responsible for deduplication and for requiring a
supermajority before a witness call reaches the pallet. The security of *all* deposits,
redemption settlements (`redeemed()` does not compare the witnessed amount to the pending
redemption total — `cf-funding/src/lib.rs:1087`), and broadcast-success accounting therefore
reduces to the integrity of:

1. the election consensus threshold (a colluding supermajority can forge/duplicate any
   observation), and
2. the per-witness deduplication (a bug that lets the same observation be counted twice, or
   an "individual component" surviving an authority-set gap and being replayed — the concern
   raised as CF-SEC-019).

Recommendation: treat the election dedup and by-hash binding (CF-SEC-018/019) as the top
validation priority. Add defense-in-depth idempotency for the highest-value witness events
(deposit tx-id seen-set, redemption amount equality check in `redeemed()`), so a single
election-layer bug is not sufficient for value minting.

### F-2 — Arbitrum CCM gas estimation divides by a witnessed value with no zero-guard — **CONFIRMED (chain-halt DoS; violates project runtime-safety rule)**

- Area: `state-chain/chains/src/arb.rs:156`.
- Impact class: runtime panic / chain halt (fund stranding), not direct theft.

```156:156:state-chain/chains/src/arb.rs
		let b = l1c.div_ceil(p);
```

`p = self.base_fee` (`:148`) comes from Arbitrum chain-tracking, which is a **witnessed**
value. `div_ceil` panics on a zero divisor, and there is no guard rejecting a zero
`base_fee` on the way into storage. Line `:147` (`self.l1_base_fee_estimate * L1_GAS_PER_BYTES`)
also uses an unchecked `*`. `calculate_ccm_gas_limit` is reached from egress fee estimation
inside `on_finalize`/`schedule_egress`, so a panic here halts block production/import.

This directly violates the repository's own rule ("Never use ... division without checks in
runtime code"). Whether `base_fee == 0` is reachable depends on Arbitrum chain-tracking
validation; if a majority of engines can ever report (or a bug can ever store) a zero base
fee, this is a consensus-reachable halt.

Recommendation: reject zero `base_fee` tracked data before storage, and use
`checked_div`/`saturating_div` with a conservative fallback in `calculate_ccm_gas_limit`.
Audit sibling chains (`eth`, `bsc`, `sol`) for the same pattern.

### F-3 — Bitcoin batch builder returns egress IDs for outputs it silently drops below dust — **CONDITIONAL (latent; not reachable at genesis config)**

- Area: `state-chain/chains/src/btc/api.rs:104-146`.
- Impact class: payout omission / reconciliation break (a user's egress is marked handled
  while no output is created).

```112:120:state-chain/chains/src/btc/api.rs
		let mut btc_outputs = vec![];
		for transfer_param in transfer_params {
			if transfer_param.amount >= BITCOIN_DUST_LIMIT {
				btc_outputs.push(BitcoinOutput {
					amount: transfer_param.amount,
					script_pubkey: transfer_param.to,
				});
				total_output_amount += transfer_param.amount;
			}
		}
```

`egress_ids` are extracted via `unzip()` **before** this filter (`:104`) and all of them are
returned with the batch (`:145`), even for transfers dropped by the `>= BITCOIN_DUST_LIMIT`
check. Downstream broadcast-success handling would then mark a dropped egress as included.

Reachability: `schedule_egress` already rejects `amount_after_fees < EgressDustLimit`
(`cf-ingress-egress/src/lib.rs:3772`, `:3811`), and genesis sets the Bitcoin `EgressDustLimit`
to exactly `BITCOIN_DUST_LIMIT` (600 sat) (`node/src/chain_spec.rs:1143`; `btc.rs:68`). So on
a correctly configured chain no transfer reaching the batch builder can be below 600 sat and
the drop branch is dead. It becomes live only if governance sets the Bitcoin egress dust
limit below 600 (the storage default is `ConstU128<1>`). This is a latent robustness bug, not
a live exploit.

Recommendation: filter `(transfer, egress_id)` pairs together so returned IDs always match
serialized outputs, or hard-fail a batch containing a below-dust output. Also switch the
`total_output_amount += ...` accumulation (`:119`) to checked/saturating addition
(overflow is infeasible with real BTC amounts, but the unchecked `+=` is gratuitous).

### F-4 — Solana CCM: user-controlled `fallback_address` receives the swapped output when the CCM egress fails a late blacklist/size check — **CONFIRMED (self-directed; misdirection/CCM-bypass, not theft of others)**

- Area: `chains/src/ccm_checker.rs` (admission) vs `sol/api.rs` blacklist (build);
  `cf-ingress-egress/src/lib.rs:2341-2361` (fallback egress).
- Impact class: CCM delivery bypass and user/UI misdirection; **not** theft of protocol or
  third-party funds.

CCM admission (`CcmChannelMetadata::to_checked` → `CcmValidityChecker::check_and_decode`,
`chains/src/lib.rs:1310`) validates size and decodes the additional data but does **not** run
the account blacklist. The blacklist (current agg key + token-vault PDA) is only applied when
the egress transaction is *built* (`sol/api.rs:401`). Solana size validation is also
optimistic about user address-lookup-table compression (CF-SEC-021). So a CCM can pass
admission, run the swap, then fail at build time, at which point the swapped **output asset**
is egressed to the CCM's `fallback_address` (`cf-ingress-egress/src/lib.rs:2344`).

Why this is not fund theft in the classic sense: the `fallback_address`, `cf_receiver`,
`additional_accounts`, and the swap destination are all chosen by whoever created the swap
request — the depositor (vault swap) or the broker the depositor selected (deposit channel).
The funds diverted to `fallback_address` are the request creator's own funds. The real risks
are (a) a UI/receiver that shows the intended destination while funds actually round-trip to
`fallback_address`, and (b) using this to get funds out *without* the CCM message ever
executing on the receiver. It is a correctness/anti-griefing issue and a receiver-side
authorization concern (compounded by CF-SEC-020, where the Solana CCM source address is
dropped, `sol/api.rs:714`), not a primitive for stealing someone else's balance.

Recommendation: run the blacklist and a pessimistic (post-ALT) size check at admission
(`to_checked`) so an un-buildable CCM is rejected up front rather than admitted-then-refunded;
bound fallback retries; and reconsider dropping the source address given receiver
authentication expectations.

### F-5 — Broadcast failure reports are not bound to the nominated broadcaster — **CONFIRMED (liveness/griefing, not theft)**

- Area: `cf-broadcast` `transaction_failed`.
- Impact class: forced retries / premature abort of an egress → stuck funds, not redirection.

`transaction_failed` accepts any signed validator origin and records that validator as a
failed broadcaster without checking it matches the current `AwaitingBroadcast` nominee/attempt
(prior CF-SEC-006 — behaviour matches source). Because aborting only stalls an egress (funds
stay in the vault; the destination cannot be changed), the worst case is liveness degradation
and delayed payouts, not theft. Still worth binding the reporter to the nominee for
accountability and to prevent a griefing minority from forcing aborts.

### F-6 — Runtime `expect`/unchecked-counter panics on rotation and counter paths — **CONFIRMED (chain-halt DoS if invariants break)**

- Area: `cf-threshold-signature` (`active_epoch_key` `.expect`, `:1773`; handover `.expect`,
  `:858`), `cf-broadcast` (`IncomingKeyAndBroadcastId ... unwrap`, `:824`), `key_rotator.rs`
  (`assert!`/`unreachable!`), `response_status.rs` (`assert!` on vote removal).
- Impact class: chain halt (fund stranding), not direct theft.

None of these are "send funds to attacker" gadgets, but each is a place where a broken
invariant halts the runtime. They should be converted to `log_or_panic!` / structured errors
per the project's runtime-safety guidance, especially the ones reachable from witness/rotation
input rather than pure internal invariants.

---

## 5. Triage of the prior report (`critical-vulnerability-review-2026-07-24.md`)

Concrete claims from the earlier report were checked against the code:

| Prior ID | Prior severity | This review's assessment |
|----------|----------------|--------------------------|
| CF-SEC-004 (`signature_success` not re-verified) | Critical | **Downgraded / false positive.** The pallet implements `validate_unsigned` (`cf-threshold-signature/src/lib.rs:1054`) and does **not** override `pre_dispatch`. FRAME's default `pre_dispatch` re-runs `validate_unsigned` (with `TransactionSource::InBlock`) during block execution/import, so the threshold signature *is* verified at dispatch time, not only in the tx-pool. A malicious block author cannot include an invalid `signature_success`; importing nodes reject the block. The doc comment at `:1082` is describing exactly this. |
| CF-SEC-003 (swap ignores unfilled input) | High/Critical | **Downgraded.** `swap_single_leg` is `#[transactional]` and treats liquidity exhaustion as `InsufficientLiquidity` (`cf-pools/src/lib.rs:1102`), rolling back; upstream fill-or-kill governs partial-fill handling. Not a silent user-fund loss. |
| CF-SEC-001 / CF-SEC-002 (credit-before-fallible AMM accounting) | Critical | **Needs the transactionality check the report itself recommends**, but note the public order extrinsics and `swap_single_leg` are transactional; the residual risk is batch/cancel paths. Not confirmed as a live theft primitive here. Worth the regression test they propose. |
| CF-SEC-012 (BTC dust vs egress IDs) | High | **Confirmed but latent** — see F-3; unreachable at genesis config (dust limit == 600), live only under governance misconfiguration. |
| CF-SEC-013 (BTC unchecked `u64 +=`) | High | **Confirmed code, infeasible overflow** — summing real BTC output amounts to `> u64::MAX` (~1.8e19 sat ≈ 184 billion BTC) cannot occur; fix is hygiene, severity is low. |
| CF-SEC-015 (Arbitrum div-by-base_fee) | Critical (runtime) | **Confirmed** — see F-2. Chain-halt DoS, contingent on a zero witnessed base fee being reachable. |
| CF-SEC-006/007/008 (broadcast failure origin, re-sign replay, historical-key recovery) | High | **Confirmed as described.** F-5 covers the failure-origin item; the re-sign/historical-key items are governance-gated trust footguns (real, but require governance). |
| CF-SEC-009/010 (egress fee/dust ordering, boosted zero post-fee) | High | **Confirmed as fund-stranding/accounting-drift**, not theft. The boosted path lacks the zero-post-fee guard the non-boosted path has; consequence is self-harm/grief, not diversion. |
| CF-SEC-018/019 (election by-hash binding, stale vote replay) | Critical | **Most important open items** — these live in the election trust boundary that F-1 shows everything depends on. Prioritise validation. |
| CF-SEC-020/021/022/023 (Solana CCM source/ALT/size/replay) | High/Critical | **Confirmed as correctness/griefing/receiver-auth issues** — see F-4. Not third-party fund theft on the State Chain side; the residual Solana-vault CPI privilege question lives in the external `chainflip-sol-contracts` repo and was out of scope. |

---

## 6. Recommendations (prioritised for fund-theft risk reduction)

1. **Harden the witness/election trust boundary (F-1, CF-SEC-018/019).** Verify by-hash
   elections recompute and compare the block-data hash; ensure individual vote components
   cannot survive an authority-set gap and be replayed on rejoin. Add defense-in-depth
   idempotency to the highest-value pallet hooks (deposit tx-id seen-set; redemption amount
   equality check in `redeemed()`).
2. **Fix the Arbitrum zero-base-fee division (F-2)** and sweep sibling chain-tracking math
   for unchecked division/multiplication; reject degenerate tracked data before storage.
3. **Make the Bitcoin batch builder filter `(transfer, egress_id)` pairs together (F-3)** so
   returned egress IDs always match serialized outputs regardless of dust-limit config.
4. **Move the Solana CCM blacklist and pessimistic size check to admission (F-4)** and
   reconsider the dropped CCM source address for receiver authentication.
5. **Bind broadcast failure reports to the nominated broadcaster (F-5)** and convert the
   rotation/counter `expect`/`assert`/`unreachable` sites (F-6) to `log_or_panic!` /
   structured errors.
6. **Add the AMM rollback regression test** proposed in CF-SEC-001/002 to lock in the
   credit-after-commit ordering for batch/cancel paths.

---

## 7. Positive assurances (what a reviewer can currently rely on)

- No unprivileged on-chain extrinsic redirects, mints, or drains funds in the reviewed
  pallets. Destinations are frozen at request creation; the threshold payload authenticates
  destination + amount + replay nonce; AMM math rounds against the swapper inside a
  transactional boundary; LP/lender/funding balances are debited-before-mint and capped.
- `signature_success` forgery via a malicious block author is not possible (default
  `pre_dispatch` re-verifies the signature) — correcting the prior report's most severe
  standalone finding.
- The remaining critical exposure is concentrated in the consensus and TSS trust boundaries
  and in governance recovery paths — which is the expected shape for a TSS-secured
  cross-chain protocol, and is where validation effort should be focused.
