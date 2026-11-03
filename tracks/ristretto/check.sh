#!/usr/bin/env bash
# Runs every check of track D and stops at the first failure.
# The dalek 5.0.0 comparison needs the crate source (README section 6). Set DALEK5 to its
# directory, or SKIP_DALEK5=1 to skip that check.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root="$here/../.."

# Tracks B and D build into the same shared library, Aeneas copy and package directory.
# The lock makes a second check wait until the first one ends.
if command -v flock > /dev/null; then
  mkdir -p "$root/shared/dalek/lean/.lake"
  exec 9> "$root/shared/dalek/lean/.lake/check.lock"
  flock 9
fi

"$root/shared/dalek/check.sh"

echo "== Rust reference tests"
(cd "$here/ref-plain" && cargo test --quiet)

echo "== The Lean copies of the reference Aeneas output have no hand edits"
diff -q "$here/ref-plain/Ref/Funs.lean" "$here/lean/RistrettoRef/Funs.lean"
diff -q "$here/ref-plain/Ref/Types.lean" "$here/lean/RistrettoRef/Types.lean"

echo "== Lean build, with the axiom and vector checks"
(cd "$here/lean" && lake build)

echo "== Name-binding check"
(cd "$here/lean"
  "$root/scripts/check-short-names.py" RistrettoRef/*.lean)

echo "== Comparison with curve25519-dalek 5.0.0"
if [ "${SKIP_DALEK5:-0}" = 1 ]; then
  echo "skipped (SKIP_DALEK5=1)"
else
  dalek5=${DALEK5:-$(ls -d "$HOME"/.cargo/registry/src/*/curve25519-dalek-5.0.0 2>/dev/null | head -1)}
  if [ -z "$dalek5" ] || [ ! -d "$dalek5" ]; then
    echo "curve25519-dalek 5.0.0 not found: set DALEK5, or SKIP_DALEK5=1" >&2
    exit 1
  fi
  "$here/compare-dalek5.py" --self-test "$root/tracks/x25519/real-dalek/curve25519-dalek" \
    "$dalek5" > /dev/null
  echo "the proved path agrees, and the self-test reports every change"
fi

echo "== All checks passed"
