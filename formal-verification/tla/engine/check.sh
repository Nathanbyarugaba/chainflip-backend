#!/usr/bin/env bash
# TLC checks for engine/ formal models.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
TLA_TOOLS="../../tools/tla2tools.jar"
[[ -f "${TLA_TOOLS}" ]] || { echo "Run ../../tools/get-tools.sh first." >&2; exit 1; }

TLC() { java -XX:+UseParallelGC -cp "${TLA_TOOLS}" tlc2.TLC -workers auto -deadlock "$@"; }

pass=0; fail=0

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
		echo "FAIL  ${cfg}" >&2
		tail -20 <<<"${out}" >&2
		fail=$((fail + 1))
	fi
}

expect_violation() {
	local spec="$1" cfg="$2" inv="$3"
	local out
	out=$(TLC -config "${cfg}" "${spec}" 2>&1) || true
	if grep -q "Invariant ${inv} is violated" <<<"${out}"; then
		echo "PASS  ${cfg} (expected violation of ${inv})"
		pass=$((pass + 1))
	else
		echo "FAIL  ${cfg} — expected violation of ${inv}" >&2
		tail -20 <<<"${out}" >&2
		fail=$((fail + 1))
	fi
}

echo "== Engine mainline =="
expect_pass CeremonyBroadcast.tla CeremonyBroadcast.cfg
expect_pass BroadcastVerification.tla BroadcastVerification.cfg
expect_pass Retrier.tla Retrier.cfg

echo
echo "== Engine finding configs (must fail) =="
expect_violation Retrier.tla RetrierLimitZero.cfg AttemptNeverStarts
expect_violation BroadcastVerification.tla BroadcastVerificationFinding.cfg \
	BlameSomeoneOnInsufficientVerif

echo
echo "engine/check.sh: ${pass} passed, ${fail} failed"
[[ ${fail} -eq 0 ]]