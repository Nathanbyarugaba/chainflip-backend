#!/usr/bin/env bash
# Downloads the pinned formal verification toolchain into this directory.
#
# Tools (pinned for reproducibility of the verification results in ../REPORT.md):
#   - TLA+ tools (TLC model checker) v1.7.4
#   - Verus 0.2026.08.02.b677dd5 (x86_64 linux) + its required rustc toolchain
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

TLA_VERSION="v1.7.4"
TLA_SHA256="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"

VERUS_VERSION="0.2026.08.02.b677dd5"
VERUS_SHA256="4c769256e888ee84bde85aae44d95c46bccbb8cf70e1d09f537b0d05fe965dee"
# Verus releases are built against one specific rustc version; see version.json in the release.
VERUS_RUST_TOOLCHAIN="1.97.1"

check_sha() {
	echo "$2  $1" | sha256sum --check --quiet
}

if [[ ! -f tla2tools.jar ]]; then
	echo "Downloading tla2tools.jar ${TLA_VERSION}..."
	curl -sSfL -o tla2tools.jar \
		"https://github.com/tlaplus/tlaplus/releases/download/${TLA_VERSION}/tla2tools.jar"
fi
check_sha tla2tools.jar "${TLA_SHA256}"
# `TLC -h` exits with code 1 by design; treat "prints usage" as success.
(java -cp tla2tools.jar tlc2.TLC -h 2>&1 || true) | grep -q "model checking" || {
	echo "TLC smoke test failed (is java installed?)" >&2
	exit 1
}
echo "TLC OK."

if [[ ! -x verus/verus ]]; then
	echo "Downloading verus ${VERUS_VERSION}..."
	curl -sSfL -o verus.zip \
		"https://github.com/verus-lang/verus/releases/download/release%2F${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip"
	check_sha verus.zip "${VERUS_SHA256}"
	unzip -qo verus.zip
	rm -rf verus verus.zip.tmp
	mv verus-x86-linux verus
	rm verus.zip
fi

if ! rustup toolchain list | grep -q "^${VERUS_RUST_TOOLCHAIN}"; then
	echo "Installing rust toolchain ${VERUS_RUST_TOOLCHAIN} (required by verus)..."
	rustup install "${VERUS_RUST_TOOLCHAIN}"
fi

SMOKE_DIR="$(mktemp -d)"
SMOKE="${SMOKE_DIR}/smoke.rs"
trap 'rm -rf "${SMOKE_DIR}"' EXIT
cat >"${SMOKE}" <<'EOF'
use vstd::prelude::*;
verus! {
	fn max(a: u64, b: u64) -> (r: u64)
		ensures r >= a, r >= b,
	{
		if a > b { a } else { b }
	}
}
fn main() {}
EOF
./verus/verus "${SMOKE}" -o "${SMOKE_DIR}/smoke" >/dev/null
echo "Verus OK."

echo "All tools ready."
