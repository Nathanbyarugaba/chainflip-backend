#!/usr/bin/env bash
# Anti-vacuity mutation testing for the TLA+ specs.
#
# Each mutation injects a specific bug into a copy of a spec and asserts that
# TLC catches it with the expected invariant/property violation. This
# demonstrates that the invariants have teeth: they fail when the modelled
# protocol is broken in a representative way.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

TLA_TOOLS="$(pwd)/../tools/tla2tools.jar"
[[ -f "${TLA_TOOLS}" ]] || { echo "Run ../tools/get-tools.sh first." >&2; exit 1; }

fail=0

# run_mutation <spec> <cfg> <expected-violation-regex> <description> <sed-expr>
run_mutation() {
	local spec="$1" cfg="$2" expected="$3" description="$4" sedexpr="$5"
	local workdir
	workdir=$(mktemp -d)
	cp "${spec}" "${cfg}" "${workdir}/"
	(cd "${workdir}" && sed -i "${sedexpr}" "${spec}")
	if cmp -s "${spec}" "${workdir}/${spec}"; then
		echo "FAIL  mutation '${description}': sed expression did not change the spec" >&2
		fail=$((fail + 1))
		rm -rf "${workdir}"
		return
	fi
	local out
	out=$(cd "${workdir}" && java -cp "${TLA_TOOLS}" tlc2.TLC -workers auto -deadlock \
		-config "${cfg}" "${spec}" 2>&1) || true
	if grep -qE "${expected}" <<<"${out}"; then
		echo "PASS  mutation '${description}' caught (${expected})"
	else
		echo "FAIL  mutation '${description}' NOT caught; TLC output tail:" >&2
		tail -20 <<<"${out}" >&2
		fail=$((fail + 1))
	fi
	rm -rf "${workdir}"
}

# 1. Authority rotation: let the rotation abort after the new keys were
#    activated (the code must never do this - funds are on the new keys).
run_mutation AuthorityRotation.tla AuthorityRotation.cfg \
	"Action property.*is violated" \
	"abort after key activation" \
	's/\/\\ phase'"'"' = "SessionRotating"$/\/\\ phase'"'"' = "Idle"/'

# 2. Broadcast lifecycle: start a broadcast attempt without registering a
#    timeout for the nominee (a broadcast could then be silently forgotten).
run_mutation BroadcastLifecycle.tla BroadcastLifecycle.cfg \
	"Invariant AttemptHasTimeout is violated" \
	"attempt without timeout registration" \
	's|/\\ timeouts'"'"' = timeouts \\union {<<id, v>>}|/\\ UNCHANGED timeouts|'

# 3. Swap DCA refund: forget to include the not-yet-chunked remaining input
#    in the refund amount.
run_mutation SwapDcaFok.tla SwapDcaFok.cfg \
	"Invariant InputConservation is violated" \
	"refund drops remaining input" \
	's/refunded + chunkAmt\[id\] + remInput + cancelled/refunded + chunkAmt[id] + cancelled/'

# 4. Boost lifecycle: allow Finalise to also credit the user again (double credit
#    on the happy path — must be caught by NoDoubleCredit).
run_mutation BoostLifecycle.tla BoostLifecycle.cfg \
	"Invariant NoDoubleCredit is violated" \
	"finalise also re-credits user" \
	'/^Finalise(id) ==/,/^[[:space:]]*\/\\ UNCHANGED <<boostAmt, userCredit, boosterLosses>>/{
		s/UNCHANGED <<boostAmt, userCredit, boosterLosses>>/userCredit'"'"' = [userCredit EXCEPT ![id] = userCredit[id] + boostAmt[id]]\n    \/\\ UNCHANGED <<boostAmt, boosterLosses>>/
	}'

if [[ ${fail} -eq 0 ]]; then
	echo "mutations.sh: all mutations caught"
else
	echo "mutations.sh: ${fail} mutation(s) NOT caught" >&2
fi
[[ ${fail} -eq 0 ]]
