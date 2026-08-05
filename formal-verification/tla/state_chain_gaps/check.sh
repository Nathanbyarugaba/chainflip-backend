#!/usr/bin/env bash
# TLC checks for previously-missed state-chain areas.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
TLA_TOOLS="../../tools/tla2tools.jar"
[[ -f "${TLA_TOOLS}" ]] || { echo "Run ../../tools/get-tools.sh first." >&2; exit 1; }

TLC() { java -XX:+UseParallelGC -cp "${TLA_TOOLS}" tlc2.TLC -workers auto -deadlock "$@"; }

pass=0; fail=0
expect_pass() {
	local spec="$1" cfg="$2" out
	if out=$(TLC -config "${cfg}" "${spec}" 2>&1) &&
		grep -q "Model checking completed. No error has been found." <<<"${out}"; then
		echo "PASS  ${cfg} ($(grep -oE '[0-9,]+ states generated, [0-9,]+ distinct states found' <<<"${out}" | tail -1))"
		pass=$((pass + 1))
	else
		echo "FAIL  ${cfg}" >&2; tail -25 <<<"${out}" >&2; fail=$((fail + 1))
	fi
}

echo "== Previously-missed state-chain areas =="
expect_pass AmmSwapConservation.tla AmmSwapConservation.cfg
expect_pass ExactValueConsensus.tla ExactValueConsensus.cfg
expect_pass LendingRepay.tla LendingRepay.cfg

echo
echo "state_chain_gaps/check.sh: ${pass} passed, ${fail} failed"
[[ ${fail} -eq 0 ]]
