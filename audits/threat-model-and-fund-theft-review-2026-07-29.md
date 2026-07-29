# Chainflip Threat Model & Critical Fund-Theft Review

**Date:** 2026-07-29  
**Scope:** State Chain runtime (`state-chain/`), engine witnessing/multisig (`engine/`), chain abstractions (`state-chain/chains/`, `foreign-chains/`)  
**Method:** Source review of fund lifecycle paths; validation of prior findings in `audits/critical-vulnerability-review-2026-07-24.md` and `frost-security-review.md`  
**Out of scope:** External smart-contract repos (ETH/ARB/SOL vault programs), social/phishing of deposit addresses, pure DoS without fund movement

---

## 1. Executive summary

Chainflip’s security model is **threshold-validator custody**: vault funds on external chains can be moved only with a threshold signature produced by the active authority set, and deposits are credited only after **supermajority witness consensus** (`⌊2n/3⌋+1`). Under an honest supermajority, there is **no confirmed permissionless critical fund-theft bug** that lets an unprivileged user mint fake deposits or forge vault withdrawals.

The highest practical fund-theft risks are therefore:

1. **Authority-set compromise** (≥ success threshold of validators) — can forge deposits and authorize egress.
2. **Governance / GovKey compromise** — can `call_as_sudo`, recover historical keys, and authorise arbitrary API calls.
3. **Boost + deep reorg** — economic theft from boosters/lenders if a prewitnessed deposit disappears after boost payout.
4. **Integrity bugs that strand or mis-attribute funds** (Bitcoin dust/egress-ID mismatch, fee-withhold-before-dust, boosted zero-amount path) — not classic “attacker drains vault,” but can cause user loss or vault accounting drift.

Prior “Critical, pending validation” claims around AMM credit-before-fail and unsigned `signature_success` were **re-examined and downgraded** for practical fund theft (see §5).

---

## 2. System overview (fund lifecycle)

```text
User deposit (source chain)
        │
        ▼
Engine witnesses / elections  ──►  cf-witnesser / cf-elections
        │                               │
        │                     EnsurePrewitnessed / EnsureWitnessed
        ▼                               ▼
cf-ingress-egress                 process_deposits /
  (channel or vault swap)         vault_swap_request
        │
        ├─(boost optional)──► cf-lending-pools (BoostApi)
        │
        ▼
cf-swapping  ──►  cf-pools (AMM)  ──►  schedule egress
        │
        ▼
cf-broadcast  ──►  cf-threshold-signature  ──►  engine/multisig
        │
        ▼
Signed egress broadcast on destination chain
        │
        ▼
Witness transaction_succeeded / elections egress success
```

### 2.1 Custody model

| Asset location | Who controls spend? |
|---|---|
| External vault / deposit channels (ETH, BTC, SOL, …) | Aggregate key via TSS (`cf-threshold-signature` + `engine/multisig`) |
| Internal swap / LP balances | State Chain storage (`cf-asset-balances`, `cf-pools`) |
| Boost / lending liquidity | `cf-lending-pools` accounting; loss socialised on lost deposits |
| Withheld ingress/egress fees | `AssetBalances::WithheldAssets` (gas-asset accrual) |

### 2.2 Consensus thresholds

| Mechanism | Threshold | Location |
|---|---|---|
| Witness call dispatch | `success_threshold_from_share_count` = `⌊2n/3⌋+1` | `utilities/src/lib.rs`, `cf-witnesser` |
| Threshold signing | Ceremony threshold from authority share count | `cf-threshold-signature`, multisig |
| Governance council | Configurable `Members.threshold` (genesis default `ceil(n/2)`) | `cf-governance` |
| Fee/tip aggregation | Median of extracted witness extras | `decompose_recompose.rs` |

---

## 3. Threat model

### 3.1 Assets

- User funds in flight (deposit → swap → egress)
- Vault balances on each supported chain
- LP free balances and open orders
- Booster / lending-pool capital
- FLIP stake / funding balances (secondary for this review)
- Threshold key shares / aggregate keys (capability to move vault funds)

### 3.2 Actors

| Actor | Capabilities | Assumed goal |
|---|---|---|
| **External user / swapper** | Deposit to channels/vaults; set destinations, refund params, CCM | Steal others’ funds or inflate own output |
| **Broker / affiliate** | Open channels; set fees; mark txs for rejection (screening) | Divert swaps, grief refunds, skim fees illicitly |
| **LP / booster / lender** | Provide liquidity; cancel orders | Drain pool via accounting bugs |
| **Single / minority validator** | Submit witness votes, signing messages, failure reports | Forge deposits, abort egress, DoS keygen |
| **Supermajority validators** | Reach witness + signing threshold | Arbitrary deposit credit + vault drain |
| **Governance council / GovKey** | Approved proposals, sudo, historical-key broadcast | Full protocol control |
| **Malicious / compromised RPC** | Feed bad chain data to engines | Panic witnessing, inconsistent votes |
| **MEV / market attacker** | Manipulate pool prices, oracle-sensitive FoK | Unfair fills / forced refunds |

### 3.3 Trust boundaries

1. **External chain ↔ Engine** — RPC/node honesty; reorg depth vs `WitnessSafetyMargin`.
2. **Engine ↔ State Chain** — validators vote; threshold gates execution.
3. **State Chain accounting ↔ Vault UTXO/balances** — internal credits must match fetchable/spendable external funds.
4. **Unsigned extrinsics** — `ValidateUnsigned` / `pre_dispatch` must bind cryptographic validity before state mutation.
5. **Governance** — outside normal user trust; treated as root-equivalent for this model.

### 3.4 STRIDE-style abuse cases (fund-focused)

| Abuse case | Preconditions | Impact |
|---|---|---|
| Fake deposit witness | ≥ success-threshold dishonest authorities | Mint internal credit → egress real vault funds |
| Destination substitution | Change destination after deposit without user consent | Theft of swap output |
| Double credit same deposit | Replay / alternate call hashes accepted | Inflated liability vs vault |
| Boost then vanish | Prewitness boost + deposit never finalises (reorg/invalid) | Booster/lender loss; attacker may keep egress |
| Forged threshold signature | Break TSS / misuse historical keys | Direct vault drain |
| AMM balance inflation | Credit LP without burning liquidity | Drain pool against other LPs/swappers |
| CCM / ALT abuse | Bypass blacklist or forge receiver auth | Unauthorized CPI / vault interaction |
| Governance misuse | Council/GovKey compromise | Arbitrary transfers via sudo / historical broadcast |

---

## 4. Critical fund-theft analysis by surface

### 4.1 Deposit witnessing & crediting — `cf-ingress-egress`

**Controls**

- `process_deposits` / `vault_swap_request` require `EnsurePrewitnessed` or `EnsureWitnessed`.
- Deposit channels bind action (destination, refund, CCM) at channel open time — witnesses supply amount/address/details, not destination.
- Vault swaps decode destination from on-chain calldata; runtime re-validates addresses and refund params (`derive_channel_action_from_vault_deposit_witness`).
- Channel recycle rejects deposits to recycled addresses (lookup miss → failure).
- Dedup of witness *calls* via `CallHashExecuted` (per epoch).

**Residual risks**

- **No per-deposit idempotency key** on the generic deposit path beyond call-hash uniqueness. Honest majority must not re-witness the same logical deposit under a different call encoding. Bitcoin UTXOs are appended via `on_deposit_made` without an obvious “already seen” reject before channel action — double-witness of the same UTXO under two call hashes would double-credit. Mitigated by honest-majority assumption + engine behaviour, not by a hard runtime invariant.
- **Boosted path** (`process_prewitness_deposit_inner`) performs `perform_channel_action` even if post-fee amount is zero; non-boosted path rejects zero. Integrity issue (confirmed in code at ~L2887–2892 vs L3216–3217).

**Fund-theft verdict:** User/broker alone cannot redirect a channel deposit. Vault-swap destination is user-chosen on-chain. Critical theft requires dishonest witness majority (or boost/reorg economics).

### 4.2 Boost — `cf-lending-pools`

**Flow:** Prewitness → `try_boosting` funds swap immediately → full witness `finalise_boost` or timeout `process_deposit_as_lost`.

**Attack:** Deposit with boost → receive egress from boosted funds → cause deposit to be treated as lost (deep reorg beyond safety margin / never finalised).

**Mitigations:** `WitnessSafetyMargin`, boost delay blocks, boost fee, timeout cleanup for vault boosts (`BoostedVaultTransactionTimeout`).

**Fund-theft verdict:** Real economic attack surface against boosters/lenders, not a pure logic bug. Severity depends on chain reorg reality (esp. BTC) and configured margins.

### 4.3 Swapping & AMM — `cf-swapping`, `cf-pools`, `state-chain/amm`

**Controls**

- FoK / min price / oracle slippage validation.
- `swap_single_leg` is `#[transactional]`; after AMM swap it requires `current_price` still exists, which fails closed when liquidity is exhausted (partial fill with remaining input typically yields `InsufficientLiquidity` and rolls back).
- Extrinsic failures roll back storage via FRAME executive.

**Prior CF-SEC-001/002 (credit before fallible fee credit):** Pattern exists — decrease burns and `credit_account`s withdrawn assets before `try_credit_account` for fees. `try_credit_account` only fails on `BalanceOverflow` (extreme). Extrinsic rollback and `#[transactional]` on limit-order updates make practical theft unlikely. **Downgraded to Medium coding-hygiene / defense-in-depth**, not confirmed critical theft.

**Prior CF-SEC-003 (ignore remaining input):** `_remaining_amount` is ignored, but post-swap `current_price` check + transactional wrapper largely prevent accepting a partial fill as a full swap. **Downgraded** unless a case is shown where remaining > 0 and `current_price` still returns `Some`.

### 4.4 Egress & broadcast — `cf-ingress-egress`, `cf-broadcast`, `cf-chains`

**Confirmed issue — Bitcoin dust / egress ID mismatch (CF-SEC-012)**

```104:146:state-chain/chains/src/btc/api.rs
		let (transfer_params, egress_ids): (Vec<TransferAssetParams<Bitcoin>>, Vec<EgressId>) =
			transfer_params.into_iter().unzip();
		// ...
		for transfer_param in transfer_params {
			if transfer_param.amount >= BITCOIN_DUST_LIMIT {
				btc_outputs.push(/* ... */);
				total_output_amount += transfer_param.amount;
			}
		}
		// ...
		Ok(vec![(Self::BatchTransfer(...), egress_ids)]) // all IDs, including filtered dust
```

Dust outputs are dropped from the tx but their egress IDs remain associated with the broadcast. Users can be marked paid without receiving an output; funds remain in vault/change. **High integrity / user-loss**; not a permissionless vault drain, but critical for payout correctness.

**Also confirmed**

- `schedule_egress` withholds fees before dust check (CF-SEC-009) — can accrue fees / start fee swaps then fail.
- `transaction_failed` accepts any validator origin (CF-SEC-006) — liveness / abort griefing, not direct theft.
- Governance `threshold_sign_and_broadcast_with_historical_key` accepts arbitrary API calls (CF-SEC-008) — **root-equivalent vault spend** if governance is compromised.

### 4.5 Threshold signatures — `cf-threshold-signature`, `engine/multisig`

**Prior CF-SEC-004 (`signature_success` unsigned):** Dispatch does not re-verify, relying on `ValidateUnsigned`. This pallet does **not** override `pre_dispatch`; FRAME default `pre_dispatch` re-invokes `validate_unsigned`, so invalid signatures should fail at block import. Unlike the historical `cf-environment` bug (custom `pre_dispatch` skipped sig checks), this path appears defended. **Downgraded** unless a bypass of `pre_dispatch` is demonstrated.

**FROST / keygen (frost-security-review.md):** Per-ceremony coefficient-length check weakened to a global byte cap after PR #3248. Impact is primarily **keygen DoS / unattributable signing failure**, not direct fund theft. Still important for threshold integrity over time.

**Supermajority of key shares** remains a hard fund-theft precondition for forging egress signatures.

### 4.6 Solana CCM / ALTs

- Blacklist checks `cf_receiver` + `additional_accounts` only (`check_ccm_for_blacklisted_accounts`); ALT *contents* are not scanned (CF-SEC-022).
- Length validation is optimistic when user ALTs are present (CF-SEC-021) — can admit unbuildable CCM → refund/fallback path.
- Source address dropped in some Solana CCM construction (CF-SEC-020) — receiver-auth weakness, not automatic vault drain.

**Fund-theft verdict:** Needs contract/program-level confirmation whether ALT-only inclusion of `agg_key` / token vault PDA enables a steal. Treat as **High pending validation**, not confirmed critical.

### 4.7 Elections / block witnesser

Prior claims (CF-SEC-018/019) about ByHash not binding block data and individual-component vote replay across authority gaps would be critical if they allow forged deposit observations without a real chain event. Not fully re-proven in this pass; keep as **priority validation items**. Deposit safety ultimately still requires dishonest or buggy witness consensus.

### 4.8 Governance

Governance can:

- `call_as_sudo` any runtime call  
- Whitelist GovKey call hashes  
- Re-sign aborted broadcasts  
- Request historical-key signatures for arbitrary API calls  

**This is intentional root.** Compromise of council threshold or GovKey is full fund theft. Not a bug; primary operational trust assumption.

---

## 5. Disposition of prior “critical” findings (fund-theft lens)

| ID | Prior severity | This review | Rationale |
|---|---|---|---|
| CF-SEC-001/002 AMM credit-before-fee | Critical pending | **Medium** | Extrinsic rollback + fee fail only on u128 overflow |
| CF-SEC-003 ignore remaining swap input | Critical/High | **Low–Medium** | Transactional + post-swap `current_price` fail-closed |
| CF-SEC-004 unsigned signature_success | Critical/High | **Low** (pending bypass hunt) | Default `pre_dispatch` re-validates |
| CF-SEC-005 keygen panic on cancel | High | **High DoS / threshold integrity** | Not direct theft |
| CF-SEC-006 any-validator tx_failed | High | **High liveness** | Not direct theft |
| CF-SEC-008 historical-key arbitrary call | High | **Critical if gov compromised** | Trusted root path |
| CF-SEC-009 fee before dust | High | **High integrity** | Stranding / accounting |
| CF-SEC-010 boosted zero post-fee | High | **High integrity** | Confirmed asymmetry |
| CF-SEC-012 BTC dust ID mismatch | High | **High user-loss / reconciliation** | Confirmed in code |
| CF-SEC-013 BTC u64 unchecked add | High | **Medium–High** | Overflow panic/wrap risk |
| CF-SEC-018/019 elections | Critical pending | **Keep critical pending** | Needs targeted proof |
| FROST coeff length | Likely regressed | **High integrity / DoS** | Not direct theft |

---

## 6. Highest-priority fund-theft scenarios (ranked)

### P0 — Trust failures (by design)

1. **≥⌊2n/3⌋+1 dishonest authorities** witness fake deposits and sign egress to attacker addresses.  
2. **Governance / GovKey compromise** uses sudo or historical-key broadcast to move vault funds.

### P1 — Confirmed or strongly evidenced protocol bugs affecting funds

3. **Bitcoin batch dust vs egress ID mismatch** — users can be treated as paid without outputs (`btc/api.rs`).  
4. **Boosted deposit with fees consuming full amount** still runs channel action — zero-amount swap/egress edge cases.  
5. **Fee withhold before dust failure** — fees taken / fee-swaps started when egress cannot proceed.

### P2 — Economic / environmental theft

6. **Boost + reorg deeper than safety margin** — attacker receives boosted egress; boosters absorb loss.  
7. **Broker / UI destination fraud** — user sends to broker-controlled channel parameters (integration trust, not runtime bug).

### P3 — Pending validation (treat as critical until disproven)

8. **Election ByHash / stale individual votes** enabling forged block observations.  
9. **Solana CCM ALT blacklist gap** enabling privileged account inclusion.  
10. **AMM / unsigned paths** if a concrete bypass of transactional/`pre_dispatch` assumptions is found.

---

## 7. Recommended hardening (fund-theft focused)

1. **Deposit idempotency:** Persist processed `(chain, tx_id/utxo)` (and vault `tx_id`) and reject double finalisation independent of call hash.  
2. **Bitcoin AllBatch:** Filter `(transfer, egress_id)` pairs together; use checked `u64` accumulation.  
3. **Boost path:** Reject zero `amount_after_fees` before `perform_channel_action` (same as non-boost).  
4. **schedule_egress:** Compute fees without side effects; only accrue after dust/viability checks.  
5. **Historical-key recovery:** Bind to stored failed-broadcast records; disallow free-form API calls.  
6. **`transaction_failed`:** Restrict reporter to current nominee (or require evidence).  
7. **Keygen:** Restore exact `threshold+1` coefficient-length check (frost review).  
8. **Elections:** Prove ByHash binds `hash(block_data)==query`; clear individual components across non-authority gaps.  
9. **Solana CCM:** Blacklist-scan resolved ALT accounts; make length checks pessimistic or post-ALT.  
10. **Defense in depth:** Re-verify threshold signature inside `signature_success` body; mark range-order updates transactional like limit orders.

---

## 8. Testing recommendations

| Test | Goal |
|---|---|
| BTC AllBatch with mixed dust/non-dust | Egress IDs ⊆ serialized outputs |
| Boost deposit where fees ≥ amount | No channel action / no zero swap |
| schedule_egress dust failure | No withheld fee / no fee-swap side effects |
| Double `process_deposits` same UTXO, different batch | Second credit rejected |
| `signature_success` invalid sig via `pre_dispatch` | Rejected at import |
| Keygen over-long / short commitments | Attributable reject, no panic |
| Boost then never finalise (vault timeout) | Loss path correct; no double finalise |

---

## 9. Conclusion

Chainflip’s fund security reduces to **honest-supermajority witnessing + intact TSS + trustworthy governance**, with user destinations fixed by channel config or on-chain vault-swap calldata. This review did **not** find a confirmed, permissionless critical bug that lets an unprivileged attacker drain vaults.

The most important **code-level fund issues** to fix next are payout/accounting correctness (especially Bitcoin dust/egress IDs), boost/fee edge cases, and the pending election/Solana validation items that could undermine the honest-majority assumption if real. Treat authority-set and governance compromise as the dominant theft scenarios for operational risk management.
