#!/usr/bin/env bash
# Verify all Chainflip formal models (F* + Lean).
# Exit non-zero on any failure.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "========================================"
echo " F* verification"
echo "========================================"
if ! command -v fstar.exe >/dev/null 2>&1; then
  echo "error: fstar.exe not on PATH" >&2
  echo "install: curl -fsSL https://aka.ms/install-fstar | bash -s -- --release" >&2
  exit 1
fi
make -C "${ROOT}/fstar" verify

echo
echo "========================================"
echo " Lean verification"
echo "========================================"
if ! command -v lake >/dev/null 2>&1; then
  # Common elan location
  if [[ -x "${HOME}/.elan/bin/lake" ]]; then
    export PATH="${HOME}/.elan/bin:${PATH}"
  else
    echo "error: lake not on PATH (install elan / Lean 4)" >&2
    exit 1
  fi
fi
(
  cd "${ROOT}/lean"
  if [[ ! -d .lake/packages/mathlib ]]; then
    echo "Fetching Mathlib (lake update)…"
    lake update
  fi
  lake build
)

echo
echo "========================================"
echo " All formal proofs verified."
echo "========================================"
