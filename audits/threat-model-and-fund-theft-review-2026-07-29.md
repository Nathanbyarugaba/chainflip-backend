# Threat Model and Fund-Theft Review — 2026-07-29

Source-level review of the Chainflip backend at `99a8bc23` (`main`, post "Flip 2.1"), aimed
specifically at vulnerabilities that let an attacker take value they are not entitled to.

**Result: one confirmed exploitable finding** (`CFT-2026-01`, High) in the Flip 2.1 delegation
code, with a proof-of-concept test committed alongside this report. Everything else that was
examined either held up or turned out to be a lower-severity robustness issue. Several findings
from the previous report (`audits/critical-vulnerability-review-2026-07-24.md`) are refuted with
evidence in [§5](#5-corrections-to-the-2026-07-24-report).

---

## 1. Method, and what "confirmed" means here

Review was source-only plus unit tests; no localnet or bouncer runs, and no live network was
touched.

A finding is only reported below if the exploit path was traced end to end in the actual code —
every origin check, every `ensure!`, every enclosing `#[transactional]` — and an attempt to
*disprove* it failed. Candidates that turned out to be guarded elsewhere are not listed as
findings; the ones that were previously reported as critical are listed in §5 with the guard that
refutes them, so the same ground doesn't get re-covered.

`CFT-2026-01` is backed by two committed tests rather than prose:

| Test | Proves |
| --- | --- |
| `pallet_cf_validator::tests::delegation::delegator_can_withdraw_stake_after_snapshot_and_still_earn_full_rewards` | The full attack sequence: stake is locked while delegating, becomes withdrawable after the auction snapshot, and the attacker still receives the same reward share as a delegator who kept their stake in place. |
| `pallet_cf_flip::tests::update_bond_is_capped_at_the_account_balance` | The step that the validator mock cannot model: `Bonder::update_bond` silently truncates the bond to the account balance, so a drained account is never retroactively locked. |

---

## 2. Threat model

### 2.1 What is worth stealing, and where it sits

| Asset | Custody | Worst case |
| --- | --- | --- |
| External-chain vault balances (BTC, ETH/ERC20, ARB, SOL, DOT/HUB) | Multi-party threshold key held collectively by the authority set | Total loss. An attacker who gets the validator set to threshold-sign a payload of their choosing drains every vault at once. |
| On-chain LP/broker asset balances | `cf-asset-balances::FreeBalances`, `cf-pools` positions | Loss of LP funds; drains the vaults indirectly on egress |
| FLIP: bonded stake, delegated stake, redemptions | `cf-flip::Account`, `cf-funding::PendingRedemptions` | Loss of stake; forged `UpdateFlipSupply` would let FLIP be minted on Ethereum |
| Per-epoch reward pot | `cf-flip` distribution reserve / block emissions | Rewards diverted away from the validators and delegators who earned them |
| In-flight deposits and swaps | `cf-ingress-egress`, `cf-swapping` | Deposits credited to the wrong account, or credited twice |

### 2.2 Actors and trust boundaries

Ordered by how much the protocol has to trust them:

1. **Anonymous user** — can submit any signed extrinsic and deposit to any address. Trusted with
   nothing. This is the actor the review focused on.
2. **Registered roles** (Broker, LP, Operator, Validator) — obtained permissionlessly by
   registering (Validator/Operator additionally require stake). Trusted only within their role.
3. **Single validator** — one vote in witnessing and elections; may be a broadcast nominee.
   Assumed potentially Byzantine.
4. **Validator supermajority (≥ ⌊2n/3⌋+1)** — *trusted by design*. Can witness anything, so can
   mint deposits and confirm egresses that never happened. Not a vulnerability class; it is the
   security assumption. Findings that require it are not reported as exploits.
5. **Governance council / tokenholder governance** — trusted with recovery powers, including
   signing arbitrary payloads with a historical key.

The boundary that matters most is 1→2→3. A finding is only interesting if an actor at level 1–3
crosses it.

### 2.3 Attack surface

Everything that can move value enters through one of five doors. The origin type on each door is
what makes it safe or not:

| Door | Origin | Who | Notes |
| --- | --- | --- | --- |
| Signed extrinsics | `ensure_signed` / `AccountRoleRegistry::ensure_*` | Anyone | The largest surface. Value-moving calls live in `cf-lp`, `cf-pools`, `cf-swapping`, `cf-funding`, `cf-validator`, `cf-lending-pools`, `cf-trading-strategy`. |
| Witnessed calls | `EnsureWitnessed` / `EnsurePrewitnessed` | Supermajority | Deposits, chain tracking, egress confirmations, redemption settlement. Trusted by assumption. |
| Elections votes | `ensure_validator` + current-authority check | Single validator | Consensus is what turns votes into facts; the threshold is the control. |
| Unsigned extrinsics | `ensure_none` + `ValidateUnsigned` | Anyone | `cf-threshold-signature::signature_success`, `cf-environment::non_native_signed_call`. |
| Governance | `EnsureGovernance` | Council | Includes deliberately dangerous recovery paths. |
| Runtime hooks | none | — | `on_initialize` / `on_finalize` / `on_idle`. No origin to check, so invariants must hold unconditionally; a panic here halts the chain. |

Two of these deserve a note because they look alarming and are not:

**Unsigned extrinsics are properly gated.** Both unsigned calls verify a signature in
`ValidateUnsigned` and not in the dispatchable body, which looks like it could be bypassed by a
malicious block author. It cannot: for bare (unsigned) extrinsics the SDK calls
`UnsignedValidator::pre_dispatch` during block *execution*, before dispatch, so every importing
node re-runs the check and rejects the block if it fails —
`substrate/primitives/runtime/src/generic/checked_extrinsic.rs:116-121`. `cf-environment`
additionally overrides `pre_dispatch` to bump the signer's nonce
(`state-chain/pallets/cf-environment/src/lib.rs:879-884`), which is what stops a signed
non-native call being replayed, since `CheckNonce` does not run for unsigned origins.

**Governance is powerful by design.** `re_sign_aborted_broadcasts`,
`threshold_sign_and_broadcast_with_historical_key`, and `dispatch_solana_gov_call` can all cause
arbitrary payloads to be signed. These are recovery tools behind `EnsureGovernance`, and are
correctly treated as trusted rather than as vulnerabilities.

### 2.4 Where the risk actually concentrated

Applying the model above, the highest-risk areas going into the review were:

1. **Flip 2.1 delegation and lending** — newest code, moves FLIP, and introduces a new
   snapshot-based accounting model. *This is where the finding is.*
2. **Threshold-signature request creation** — one reachable path with an attacker-chosen payload
   would be catastrophic. Every `request_signature` / `threshold_sign_and_broadcast` call site was
   enumerated; all originate from protocol hooks, witnessed state, or governance.
3. **Deposit crediting and boost** — the mint-from-nothing surface.
4. **AMM and LP balance accounting** — credit/debit ordering and rounding direction.
5. **Elections** — the layer that turns validator votes into facts.

---

## 3. Confirmed finding

### CFT-2026-01 — Delegated stake can be withdrawn after the snapshot that pays and slashes it

- **Severity: High.** Directly profitable, permissionless, repeatable each epoch, and it also
  degrades the authority set's bond. Not Critical: it cannot drain a vault, and the profit per
  epoch is bounded by the delegator portion of that epoch's reward pot.
- **Area:** `state-chain/pallets/cf-validator` (delegation), `state-chain/pallets/cf-flip`
  (bonding), `state-chain/pallets/cf-funding` (redeem / rebalance).
- **Impact class:** reward theft from honest stakers; slashing evasion; under-collateralised
  authority set.
- **Attacker requirements:** one unregistered account holding FLIP. No role, no stake history, no
  validator or broker privileges. The FLIP only has to be present for a single, publicly
  observable block, so it can be borrowed.

#### The gap

A delegator's pledged stake is held in place by exactly two mechanisms, and there is a window in
which neither applies.

The first is the `max_bid` reservation, which is keyed on the *live* `DelegationChoice` entry:

```2461:2480:state-chain/pallets/cf-validator/src/lib.rs
	fn ensure_can_redeem_amount(
		validator_id: &Self::ValidatorId,
		amount: Self::Amount,
	) -> DispatchResult {
		Self::ensure_not_active_bidder_during_auction(validator_id)?;
		// A delegator may redeem from the portion of their balance that is not
		// reserved by their stored max_bid — the amount visible to the auction
		// (capped at max_bid) cannot drop, but funds the user never pledged
		// remain freely redeemable.
		if let Some((_, max_bid)) = DelegationChoice::<T>::get(<ValidatorIdOf<T> as IsType<
			T::AccountId,
		>>::into_ref(validator_id))
		{
			let balance = T::FundingInfo::balance(
				<ValidatorIdOf<T> as IsType<T::AccountId>>::into_ref(validator_id),
			);
			ensure!(balance.saturating_sub(amount) >= max_bid, Error::<T>::StillBidding);
		}
		Ok(())
	}
```

`undelegate` removes that entry immediately, with no rotation-phase guard
(`state-chain/pallets/cf-validator/src/lib.rs:1357-1405`), after which the check above is a no-op.
The auction-phase guard does not cover delegators either — it only tests membership of
`ActiveBidder`, which holds bidding *validators*
(`state-chain/pallets/cf-validator/src/lib.rs:2445-2454`).

The second mechanism is the bond, and it is applied only at the epoch transition, from the
snapshot:

```1761:1793:state-chain/pallets/cf-validator/src/lib.rs
		let mut new_delegator_bids = BTreeMap::new();
		let mut managed_validator_bonds = BTreeMap::new();
		for (_, snapshot) in DelegationSnapshots::<T>::iter_prefix(new_epoch) {
			managed_validator_bonds.extend(snapshot.validator_bond_distribution(new_bond));
			new_delegator_bids.extend(snapshot.delegators.clone());
		}
		// ... elided ...
		for (delegator, bid) in new_delegator_bids {
			T::Bonder::update_bond(&delegator.clone().into(), bid);
		}
```

and `update_bond` silently truncates to whatever the account holds at that instant:

```694:699:state-chain/pallets/cf-flip/src/lib.rs
	fn update_bond(account_id: &Self::AccountId, new_bond: Self::Amount) {
		Account::<T>::mutate(account_id, |FlipAccount { balance, bond }| {
			*bond = core::cmp::min(new_bond, *balance);
		});
		Pallet::<T>::deposit_event(Event::BondUpdated { account_id: account_id.clone(), new_bond });
	}
```

The snapshot itself is written when the auction resolves — several blocks *before* the transition
that applies the bond (`VAULT_ROTATION_BLOCKS` is 12, and more if keygen has to retry):

```1936:1941:state-chain/pallets/cf-validator/src/lib.rs
				// Register the delegation snapshots for the next epoch.
				let next_epoch_index = CurrentEpoch::<T>::get() + 1;
				DelegationSnapshot::clear_epoch_registrations::<T>(next_epoch_index);
				for snapshot in delegation_snapshots.into_values() {
					snapshot.register_for_epoch::<T>(next_epoch_index);
				}
```

and it is never revisited afterwards. Reward shares are computed straight from the recorded
amount, deliberately uncapped:

```267:272:state-chain/pallets/cf-validator/src/delegation.rs
		let delegator_cuts = self.delegators.iter().map(move |(delegator, individual_stake)| {
			// Note we need to use the *uncapped* total delegator stake here to determine shares.
			let share =
				Perquintill::from_rational((*individual_stake).into(), total_delegator_stake);
			(delegator, share * delegators_cut)
		});
```

So in the window between auction resolution and the epoch transition, the pledge is unenforced in
both directions: `DelegationChoice` can be deleted, and the bond has not been applied yet.

#### Attack

1. Fund a fresh account with `N` FLIP and call `delegate(operator, Max)`, so
   `DelegationChoice = (operator, N)`. Any operator with `DelegationAcceptance::Allow` will do.
2. Wait for the auction to resolve at the end of the current epoch. `build_delegation_snapshots`
   records the delegator at `min(max_bid, balance) = N`
   (`state-chain/pallets/cf-validator/src/lib.rs:2227-2234`). This block is public and
   predictable — it is the `AuctionCompleted` event.
3. In any block before the epoch transition completes, call `undelegate(Max)`. The
   `DelegationChoice` entry is removed, so the `max_bid` reservation no longer applies, and the
   bond is still whatever it was in the previous epoch (zero for a new delegator).
4. Move the stake out, leaving only `MinimumFunding`. Either `redeem`, which debits immediately
   via `try_initiate_redemption` after `ensure_can_redeem_amount` now passes
   (`state-chain/pallets/cf-funding/src/lib.rs:687-700`), or — faster, with no Ethereum round trip
   — `rebalance` to a second account, which is gated by `ensure_can_transfer` and that check is
   also keyed on the now-deleted `DelegationChoice`
   (`state-chain/pallets/cf-funding/src/lib.rs:847-889`,
   `state-chain/pallets/cf-validator/src/lib.rs:2482-2501`).
5. The epoch begins. `update_bond(delegator, N)` truncates to the remaining dust, so nothing is
   locked.
6. At the end of the epoch, `on_epoch_ending` distributes the whole accumulated reward pot through
   the epoch's snapshots (`state-chain/runtime/src/chainflip/epoch_transition.rs:27-38`,
   `state-chain/pallets/cf-flip/src/lib.rs:561-604`,
   `state-chain/pallets/cf-validator/src/delegation.rs:390-410`), and the attacker is paid on `N`.

Because the capital only has to be present for one predictable block, it can be borrowed. An
attacker who temporarily supplies most of an operator's delegated stake at the auction block
captures most of that operator's delegator reward share for the entire epoch at approximately zero
capital cost and zero risk — diluting the delegators and validators who actually locked capital
for the epoch. The two effects compound, because the same borrowed stake also inflates the
operator's `avg_bid` and can push more of their validators into the authority set, raising the
`authority_count` multiplier the group is paid on.

#### Secondary consequences

Two further consequences follow from the same root cause, and are worth fixing together with it:

**Slashing evasion.** A managed validator's slash is split across their snapshot rather than taken
from the validator (`state-chain/pallets/cf-validator/src/delegation.rs:430-437`, wired as
`DelegationSlasher<Runtime, FlipSlasher<Runtime>>` in
`state-chain/runtime/src/configs.rs:848`). `Flip::slash` silently does nothing when the target
cannot cover its share:

```542:553:state-chain/pallets/cf-flip/src/lib.rs
	fn slash(account_id: &T::AccountId, slash_amount: T::Balance) {
		if !slash_amount.is_zero() && Account::<T>::get(account_id).can_be_slashed(slash_amount) {
			Pallet::<T>::settle(
				account_id,
				Pallet::<T>::burn_or_deposit_to_reserve(slash_amount).into(),
			);
			Self::deposit_event(Event::<T>::SlashingPerformed {
				who: account_id.clone(),
				amount: slash_amount,
			})
		}
	}
```

So the portion of any slash allocated to the drained delegator is never collected, and the
operator's group is under-punished in proportion to the stake that left. An operator can therefore
buy cheap slashing insurance for a whole epoch.

**Under-collateralised authority set.** The auction chose the winners and set the bond using the
snapshot's delegated stake. `validator_bond_distribution` bonds each managed validator only up to
its *own* bid (`state-chain/pallets/cf-validator/src/delegation.rs:226-238`); the rest of the
group's economic backing is supposed to come from the delegator bonds. If those evaporate before
the epoch starts, the group is bonded well below `bond × n` for the whole epoch, and the network's
slashing collateral is less than the protocol believes it to be.

#### Scope of exposure

The delegator reward path is live in both configurations, so this is not gated on Flip 2.1
activation:

- Post-activation, the fee-reward pot is distributed via `distribute_all`
  (`state-chain/runtime/src/chainflip/epoch_transition.rs:27-38`).
- Pre-activation (`FeeRewardsActivationEpoch` defaults to `u32::MAX`), block-author emissions are
  already routed through the same snapshot by `DelegatedRewardsDistribution`
  (`state-chain/pallets/cf-emissions/src/lib.rs:347-364`,
  `state-chain/runtime/src/configs.rs:812`).

Slashing goes through the snapshot in both cases. Please confirm per network whether delegation is
enabled and whether any operator is set to `DelegationAcceptance::Allow`, since that determines
whether the path is reachable today rather than only after rollout.

#### Suggested remediation

The root cause is that the pledge is only enforced against live `DelegationChoice` state, while
the snapshot that pays and slashes is fixed earlier. Two independent fixes, ideally both:

1. **Keep the pledge binding for as long as the snapshot binds** (preferred — this is the one that
   also fixes slashing evasion and bond integrity). Have `ensure_can_redeem_amount` and
   `ensure_can_transfer` honour the pending next-epoch snapshot as well as `DelegationChoice`: if
   `DelegationSnapshots(CurrentEpoch + 1, _)` records the account as a delegator, require
   `balance - amount >= recorded_bid` regardless of whether `DelegationChoice` still exists. This
   closes the window without changing reward semantics, and preserves the intended behaviour that
   a mid-epoch `undelegate` still earns for the epoch it backed (which
   `cf-integration-tests::rewards` asserts deliberately).
2. **Make the payout reflect what was actually bonded** (defence in depth). At the epoch
   transition, when the bond is truncated by `update_bond`, write the truncated amount back into
   the snapshot so reward and slash shares are computed on stake that was genuinely locked. This
   contains the damage if the window is ever reopened, and makes the snapshot self-consistent with
   the bonds derived from it.

A regression test should assert zero delegator reward for the sequence delegate → snapshot →
undelegate → withdraw → epoch. The committed proof-of-concept test can be inverted to serve as
that test once a fix lands.

---

## 4. Lower-severity observations

Verified, but none is fund theft. Listed because each is a latent correctness or runtime-safety
issue in a value-carrying path.

### CFT-2026-02 — Unchecked `div_ceil` by tracked `base_fee` on Arbitrum (runtime safety)

`state-chain/chains/src/arb.rs:156` computes `l1c.div_ceil(p)` with `p = self.base_fee` and no zero
guard, and line 147 multiplies `l1_base_fee_estimate` with an unchecked `*`. `cf-chain-tracking`
places no lower bound on tracked fee data — `inner_update_fee` overwrites `tracked_data`
unconditionally (`state-chain/pallets/cf-chain-tracking/src/lib.rs:210-220`) and
`ArbitrumTrackedData::default()` is all zeroes. The reachable caller is CCM gas-limit estimation
in `state-chain/runtime/src/chainflip.rs:317-325`, which handles a *missing* chain state but not a
zero `base_fee`.

Arbitrum's base fee has a protocol floor, so honest witnessing should never produce zero; the
concern is that nothing in the runtime enforces that. Per `CLAUDE.md` ("never use division without
checks in runtime code"), this should be a `checked_div` with a conservative fallback, or a
non-zero validation when tracked data is stored. Worth checking the other chains' `TrackedData`
for the same pattern.

### CFT-2026-03 — Bitcoin egress dust filter can silently drop an output while still reporting its egress ID

`state-chain/chains/src/btc/api.rs:104-146` unzips `(transfer, egress_id)` pairs *before* filtering
outputs below `BITCOIN_DUST_LIMIT`, then returns the full `egress_ids` list alongside a transaction
that omits the dust outputs. A dropped payment would be recorded as broadcast, and the amount would
stay in the vault.

Not currently reachable: `schedule_egress` already rejects below-dust egresses using
`EgressDustLimit` (`state-chain/pallets/cf-ingress-egress/src/lib.rs:3772`, `3811`), and the chain
spec sets that limit for BTC to exactly `BITCOIN_DUST_LIMIT`
(`state-chain/node/src/chain_spec.rs:1143`). The issue is the coupling: two independently
configured thresholds have to stay in lockstep, and the failure mode if they ever diverge is
silent loss rather than an error. Filtering the `(transfer, egress_id)` pairs together — or
rejecting the batch outright — removes the dependency.

The neighbouring `total_output_amount += transfer_param.amount` on `u64`
(`state-chain/chains/src/btc/api.rs:111,119`) is unchecked, but it needs the batch total to exceed
`u64::MAX` satoshis, which is ~10⁴ times the entire Bitcoin supply. Worth a `checked_add` for
hygiene; it is not a live risk, and the previous report's High rating for it was too high.

### CFT-2026-04 — `swap_single_leg` discards the AMM's unfilled input

```1122:1123:state-chain/pallets/cf-pools/src/lib.rs
				let (output_amount, _remaining_amount) =
					pool.pool_state.swap(order, input_amount, None);
```

The AMM supports partial fills and returns the unconsumed input, which is dropped. The caller in
`cf-swapping` treats the returned output as the result for the whole input, so a swap that exhausts
liquidity mid-way would pay out on the filled portion only, with no refund of the remainder.

Two things make this hard to hit and self-limiting rather than exploitable: `current_price` returns
`None` when liquidity is gone, which errors out with `InsufficientLiquidity` and rolls back; and
the `MaximumPriceImpact` check computes the effective price from the *requested* input rather than
the consumed input (lines 1130-1150), so a partial fill looks worse than it is and the check fails
closed. The direction of any residual error is user loss, not attacker gain. Still worth making
explicit: either reject a non-zero remainder, or return it so the caller can refund it.

### CFT-2026-05 — Defence in depth on witnessed deposits

`process_full_witness_deposit_inner` credits deposits without an on-chain uniqueness check on
`deposit_details` (`state-chain/pallets/cf-ingress-egress/src/lib.rs:3145-3146`), and for Bitcoin
`add_bitcoin_utxo_to_list` appends unconditionally
(`state-chain/pallets/cf-environment/src/lib.rs:1034-1036`). Deduplication lives entirely in the
elections block witnesser, and the team has already analysed the one narrow reorg-plus-recycling
case in a comment at `state-chain/runtime/src/chainflip/witnessing/bitcoin_elections.rs:222-233`.
Similarly, `Error::AssetMismatch` is defined
(`state-chain/pallets/cf-ingress-egress/src/lib.rs:1231`) but never returned — the witnessed asset
is not compared against the channel's configured asset.

This is not exploitable without witness-layer failure, so it is not a finding under the trust
model in §2.2. But deposit crediting is the mint-from-nothing path, and it currently has no
on-chain backstop. An idempotency set keyed on chain-specific deposit identity (BTC `tx_id`+`vout`,
EVM tx hash + log index), a `block_height ∈ (opened_at, expires_at]` bound, and activating the
existing `AssetMismatch` check would each bound the damage from an upstream bug independently of
the elections layer.

---

## 5. Corrections to the 2026-07-24 report

`audits/critical-vulnerability-review-2026-07-24.md` lists 23 findings, several rated Critical, and
states up front that they are unvalidated hypotheses. Re-checking them against the code refutes the
most severe ones. This matters beyond tidiness: `SECURITY.md` explicitly asks for accurate,
verified reports, and the Critical ratings in that document would otherwise absorb triage effort
that `CFT-2026-01` deserves.

| Prior finding | Verdict |
| --- | --- |
| **CF-SEC-001/002** — AMM credits LP before fallible fee processing | **Refuted.** Range-order mints debit inside the AMM's `try_debit` callback *before* any state is written, and the AMM documents that a callback error leaves state untouched (`state-chain/amm/src/range_orders.rs:687-696`). Limit-order mutations happen inside a single `Pools::try_mutate` closure, and the hook-dispatched path carries `#[transactional]` with an explanatory comment and a regression test (`state-chain/pallets/cf-pools/src/lib.rs:1755-1759`, `tests.rs::scheduled_update_below_min_fails_and_rolls_back`). Extrinsics roll back on `Err` regardless. |
| **CF-SEC-003** — pool swap ignores unfilled input | **Downgraded**, see CFT-2026-04. Real, but user loss with two indirect guards, not fund theft. |
| **CF-SEC-004** — `signature_success` not re-verified at dispatch | **Refuted.** `ValidateUnsigned::pre_dispatch` runs during block execution for bare extrinsics (`checked_extrinsic.rs:116-121`), so a malicious block author cannot bypass it — importing nodes reject the block. The pallet does not override `pre_dispatch`, so the default delegates to `validate_unsigned(InBlock, …)`, which verifies the threshold signature against the stored ceremony payload (`state-chain/pallets/cf-threshold-signature/src/lib.rs:1050-1069`). |
| **CF-SEC-006** — broadcast failure reports accepted from any validator | **Downgraded.** Aborting requires reports from *every* current authority, not merely "enough" (`state-chain/pallets/cf-broadcast/src/lib.rs:1094-1095`), so a minority cannot abort a broadcast. Tightening the reporter to the current nominee is still reasonable hardening. |
| **CF-SEC-007/008** — governance re-signing and historical-key recovery | **Not vulnerabilities.** Both are `EnsureGovernance`. Governance is a trusted actor per §2.2; these are recovery tools, and calling them footguns is a design observation, not a finding. |
| **CF-SEC-012** — BTC dust filter returns all egress IDs | **Downgraded**, see CFT-2026-03. Not reachable with the shipped dust-limit configuration. |
| **CF-SEC-013** — BTC `u64` output summation | **Downgraded.** Requires a batch total ~10⁴× the Bitcoin supply. Hygiene, not High. |
| **CF-SEC-015** — Arbitrum division by `base_fee` | **Confirmed as runtime safety**, see CFT-2026-02. Not fund theft, and denial of service is out of scope per `SECURITY.md`; still worth fixing under the runtime-safety rules in `CLAUDE.md`. |
| **CF-SEC-018** — `ByHash` elections don't verify the block data matches the hash | **Refuted as an exploit.** Block *content* is intentionally not hash-checked on-chain — that is what the supermajority threshold is for. Wrong-hash *election* responses are rejected: `validate` requires the correct response shape (`state-chain/pallets/cf-elections/src/electoral_systems/block_witnesser/state_machine.rs:254-266`) and `mark_election_done` rejects consensus whose query hash differs from the ongoing election's (`.../block_witnesser/primitives.rs:271-279`). A minority cannot push wrong data through. |
| **CF-SEC-019** — stale individual vote components replay-counted on rejoin | **Refuted.** Consensus is assembled only from `current_authorities` (`state-chain/pallets/cf-elections/src/lib.rs:871-880`), and every full consensus recheck *deletes* components belonging to non-authorities (`.../lib.rs:913-926`). The epoch-keyed cache guarantees a full recheck after rotation (`.../lib.rs:845-847`). A rejoining validator must vote again. The comment the prior report cites (`.../lib.rs:1128-1137`) describes storage retention, not vote counting. |
| **CF-SEC-005, 016, 017** — engine panics, witnessing DoS | **Out of scope.** `SECURITY.md` excludes denial of service with no financial benefit, including engine and node panics. Worth fixing as robustness. |

The remaining prior findings (CF-SEC-009/010/011/014/020/021/022/023) were not re-verified in
depth. CF-SEC-020 (Solana CCM source address) and CF-SEC-022 (blacklist not applied to
user-supplied ALT contents) are the two most worth a second look, since both concern what a CCM
receiver can authenticate; note that user-supplied ALTs must themselves pass election witnessing
before use (`state-chain/chains/src/sol/api.rs:132-137`), which constrains CF-SEC-022.

---

## 6. Reviewed without a confirmed finding

Each area below was traced against the model in §2 — origins on every extrinsic, credit/debit
ordering, transactionality, and rounding direction — with no exploitable path found. The specific
control that holds is named so this can be re-checked cheaply after future changes.

| Area | Control that holds |
| --- | --- |
| Threshold-signature request creation | Every `request_signature` / `threshold_sign_and_broadcast` call site originates from a protocol hook, witnessed state, or governance. Callbacks require the pallet-private `EnsureThresholdSigned`; no signed extrinsic can register or invoke one. |
| Replay protection per chain | EVM payloads bind nonce, chain ID, key-manager and contract address (`state-chain/chains/src/evm/api.rs:61-75`, `263-268`). Bitcoin binds all inputs and outputs in the BIP-341 sighash, and change always goes to a protocol-derived address. Solana consumes a durable nonce per transaction. Polkadot binds genesis hash and proxy nonce. |
| `cf-swapping` | Swaps are removed from `ScheduledSwaps` before execution; execution is `#[transactional]`; output and refund destinations are fixed at channel creation; internal swaps bind the credit and refund account to the signer; broker fees are capped at 1000 bps at validation and again by the available stable amount at execution. |
| `cf-pools` / `cf-amm` / `cf-asset-balances` / `cf-lp` / `cf-trading-strategy` | Rounding favours the pool on both mint (ceil debit) and burn (floor credit). Fee-growth checkpoints are set on every mint and burn, so a new position collects nothing on first touch. Every LP extrinsic keys storage on the signer; strategy sub-accounts are domain-separated Blake2 derivations. |
| `cf-ingress-egress` | Deposits enter only through witness origins. Boost double-credit is blocked by `BoostStatus` guards and exact-amount matching on finalisation. `schedule_egress` is trait-only, with no signed entry point. Refund destinations come from the channel action, not from the broker who flags a transaction. |
| `cf-lending-pools` | Boost shares are frozen at loan creation, so a late joiner neither shares the loss nor captures the fee. `BoostedDeposits::take` makes finalise-and-lose mutually exclusive. Borrow-time LTV requires fresh oracle prices and rejects zero. `remove_lender_funds` is `#[transactional]` and capped by the LTV surplus. |
| `cf-funding` / `cf-flip` | Redemption is capped by `max(bond, restricted)`; one pending redemption per account; `redeemed` and `redemption_expired` both `take` it. Imbalances revert on drop, so a dropped mint cannot create FLIP. |
| `cf-elections` | Votes require validator origin plus current-authority membership; `take_vote_and_then` replaces rather than appends; consensus is assembled once per authority against a live authority count with a ⌊2n/3⌋+1 threshold; `SharedData` is stored under a recomputed hash. |
| `cf-emissions` | `Issuance::mint` is reachable only from the block-authorship hook. The `UpdateFlipSupply` payload is read from live `TotalIssuance`, never from a caller. |
| `cf-tokenholder-governance` | Backing weight is summed from *live* balances at resolution, so splitting or moving FLIP between accounts during the voting period does not multiply it. |
| `cf-account-roles` | Deregistration checks require zero balances, no open orders, and no lending/strategy state across every fund-holding pallet. `as_sub_account` derives the sub-account from the caller's own id. |

---

## 7. Not covered

Out of scope for this pass, and the residual risk is unquantified:

- **The engine** (`engine/`), including the multisig implementation. Only the state chain and
  `state-chain/chains` were reviewed. `frost-security-review.md` covers the signing protocol.
- **The smart contracts.** The Ethereum, Arbitrum, and Solana vault contracts live in separate
  repositories. Any conclusion above about what a signed payload authorises depends on the
  contract-side checks, which were not read. `CFT-2026-03` and the CCM findings in particular
  would benefit from confirmation against the contracts.
- **Economic and MEV analysis.** Sandwiching, oracle-latency arbitrage, and liquidation-auction
  design were only examined for accounting bugs, not for economic soundness.
- **Migrations.** Storage migrations were not reviewed, and a migration that mis-shapes balance
  storage is its own theft vector.
- **Runtime API and RPC.** Reviewed only where reachable from an extrinsic.
