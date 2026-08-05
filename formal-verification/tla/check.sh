#!/usr/bin/env bash
# Runs every TLC model check for the state-chain TLA+ specs:
#   1. mainline safety/liveness configs        - must pass;
#   2. "finding" configs                       - must fail with the documented
#      invariant violation (they demonstrate real code-level issues, see
#      ../REPORT.md "Findings");
#   3. spec mutations (./mutations.sh)         - must fail, demonstrating that
#      the invariants are not vacuous.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

TLA_TOOLS="../tools/tla2tools.jar"
[[ -f "${TLA_TOOLS}" ]] || { echo "Run ../tools/get-tools.sh first." >&2; exit 1; }

TLC() {
	java -XX:+UseParallelGC -cp "${TLA_TOOLS}" tlc2.TLC -workers auto -deadlock "$@"
}

pass=0
fail=0

expect_pass() {
	local spec="$1" cfg="$2"
	local out
	if out=$(TLC -config "${cfg}" "${spec}" 2>&1) &&
		grep -q "Model checking completed. No error has been found." <<<"${out}"; then
		local stats
		stats=$(grep -oE "[0-9,]+ states generated, [0-9,]+ distinct states found" <<<"${out}" | tail -1)
		echo "PASS  ${cfg} (${stats})"
		pass=$((pass + 1))
	else
		echo "FAIL  ${cfg} - expected a successful check:" >&2
		tail -30 <<<"${out}" >&2
		fail=$((fail + 1))
	fi
}

expect_violation() {
	local spec="$1" cfg="$2" invariant="$3"
	local out
	out=$(TLC -config "${cfg}" "${spec}" 2>&1) || true
	if grep -q "Invariant ${invariant} is violated" <<<"${out}"; then
		echo "PASS  ${cfg} (expected violation of ${invariant} found)"
		pass=$((pass + 1))
	else
		echo "FAIL  ${cfg} - expected TLC to report a violation of ${invariant}:" >&2
		tail -30 <<<"${out}" >&2
		fail=$((fail + 1))
	fi
}

echo "== Mainline configurations (must pass) =="
expect_pass AuthorityRotation.tla AuthorityRotation.cfg
expect_pass AuthorityRotation.tla AuthorityRotationLarge.cfg
expect_pass AuthorityRotation.tla AuthorityRotationLiveness.cfg
expect_pass BroadcastLifecycle.tla BroadcastLifecycle.cfg
expect_pass BroadcastLifecycle.tla BroadcastLifecycleLiveness.cfg
expect_pass SwapDcaFok.tla SwapDcaFok.cfg
expect_pass SwapDcaFok.tla SwapDcaFokTwoInFlight.cfg
expect_pass SwapDcaFok.tla SwapDcaFokLiveness.cfg
expect_pass BrokerFeeSplit.tla BrokerFeeSplit.cfg
expect_pass BoostLifecycle.tla BoostLifecycle.cfg

echo
echo "== Finding configurations (must fail with the documented violation) =="
expect_violation BroadcastLifecycle.tla BroadcastLifecycleSigningFailure.cfg BarrierBacked
expect_violation SwapDcaFok.tla SwapDcaFokDoubleFailure.cfg InputConservation
expect_violation BrokerFeeSplit.tla BrokerFeeSplitFinding.cfg NoOverchargeOnAllModes
expect_violation BoostLifecycle.tla BoostLifecycleFinding.cfg NoDoubleCredit

echo
echo "== Spec mutations (anti-vacuity, must be caught) =="
./mutations.sh && pass=$((pass + 1)) || fail=$((fail + 1))

echo
echo "check.sh: ${pass} passed, ${fail} failed"
[[ ${fail} -eq 0 ]]
