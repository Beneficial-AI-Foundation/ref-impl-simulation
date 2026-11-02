#!/usr/bin/env bash
# Runs every check of track B and stops at the first failure.
# The dalek 5.0.0 comparison needs the crate source (README section 8). Set DALEK5 to its
# directory, or SKIP_DALEK5=1 to skip that check.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root="$here/../.."

echo "== Rust reference tests"
(cd "$here/ref-plain" && cargo test --quiet)

echo "== Lean build, with the axiom and vector checks"
(cd "$here/lean" && lake build)

echo "== Name-binding check"
"$root/scripts/tests/test-check-short-names.sh"
(cd "$here/lean"
  for d in X25519Ref Curve25519Dalek; do
    "$root/scripts/check-short-names.py" $(ls "$d"/*.lean | grep -v _Template)
  done)

echo "== Comparison with curve25519-dalek 5.0.0"
if [ "${SKIP_DALEK5:-0}" = 1 ]; then
  echo "skipped (SKIP_DALEK5=1)"
else
  dalek5=${DALEK5:-$(ls -d "$HOME"/.cargo/registry/src/*/curve25519-dalek-5.0.0 2>/dev/null | head -1)}
  if [ -z "$dalek5" ] || [ ! -d "$dalek5" ]; then
    echo "curve25519-dalek 5.0.0 not found: set DALEK5, or SKIP_DALEK5=1" >&2
    exit 1
  fi
  "$here/compare-dalek5.py" --self-test "$here/real-dalek/curve25519-dalek" "$dalek5" > /dev/null
  echo "the proved path agrees, and the self-test reports every change"
fi

echo "== All checks passed"
