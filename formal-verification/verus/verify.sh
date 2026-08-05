#!/usr/bin/env bash
# Verifies the Verus crate. Requires ../tools/get-tools.sh to have been run.
#
# Also asserts that no proof escape hatches (assume/admit/external_body) are
# used: every reported "verified" item is backed by a complete machine-checked
# proof.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

VERUS="../tools/verus/verus"
[[ -x "${VERUS}" ]] || { echo "Run ../tools/get-tools.sh first." >&2; exit 1; }

if out=$(rg -n "\bassume\b|\badmit\b|external_body" src/ 2>/dev/null); then
	echo "Proof escape hatches found:" >&2
	echo "${out}" >&2
	exit 1
fi

result=$("${VERUS}" src/lib.rs --crate-type=lib 2>&1)
echo "${result}"
grep -qE "verification results:: [0-9]+ verified, 0 errors" <<<"${result}"
