#!/usr/bin/env bash
# Runs every check of track B and stops at the first failure.
# The comparison with libsignal's versions needs the sources of curve25519-dalek 5.0.0 and
# x25519-dalek 3.0.0 (README section 8). Set DALEK5 and X25519_DALEK3 to their directories,
# or SKIP_DALEK5=1 to skip that check. Set REPLAY_EXTRACTION=1 to also run Charon and Aeneas
# again on x25519-dalek and on the shared library, and compare their output with the files.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root="$here/../.."

# Tracks B and D build into the same shared library, Aeneas copy and package directory.
# The lock makes a second check wait until the first one ends.
if ! command -v flock > /dev/null; then
  echo "flock not found: install util-linux, so that the checks of tracks B and D do not build at the same time" >&2
  exit 1
fi
mkdir -p "$root/shared/dalek/lean/.lake"
exec 9> "$root/shared/dalek/lean/.lake/check.lock"
flock 9

"$root/shared/dalek/check.sh"

echo "== Rust reference tests"
(cd "$here/ref-plain" && cargo test --quiet)

if [ "${REPLAY_EXTRACTION:-0}" = 1 ]; then
  echo "== The x25519-dalek extraction gives real-x25519/X25519"
  "$here/extract-real.sh" --check
fi

echo "== The Lean copies of the Aeneas output have no hand edits"
for f in Funs Types; do
  diff -q "$here/ref-plain/Ref/$f.lean" "$here/lean/X25519Ref/$f.lean"
  diff -q "$here/real-x25519/X25519/$f.lean" "$here/lean/X25519Dalek/$f.lean"
done

echo "== Lean build, with the axiom and vector checks"
(cd "$here/lean" && lake build)

echo "== Name-binding check"
"$root/scripts/tests/test-check-short-names.sh"
(cd "$here/lean"
  for d in X25519Ref X25519Dalek; do
    "$root/scripts/check-short-names.py" $(ls "$d"/*.lean | grep -v _Template)
  done)

echo "== Comparison with curve25519-dalek 5.0.0 and x25519-dalek 3.0.0"
if [ "${SKIP_DALEK5:-0}" = 1 ]; then
  echo "skipped (SKIP_DALEK5=1)"
else
  dalek5=${DALEK5:-$(ls -d "$HOME"/.cargo/registry/src/*/curve25519-dalek-5.0.0 2>/dev/null | head -1)}
  x25519dalek3=${X25519_DALEK3:-$(ls -d "$HOME"/.cargo/registry/src/*/x25519-dalek-3.0.0 2>/dev/null | head -1)}
  if [ -z "$dalek5" ] || [ ! -d "$dalek5" ]; then
    echo "curve25519-dalek 5.0.0 not found: set DALEK5, or SKIP_DALEK5=1" >&2
    exit 1
  fi
  if [ -z "$x25519dalek3" ] || [ ! -d "$x25519dalek3" ]; then
    echo "x25519-dalek 3.0.0 not found: set X25519_DALEK3, or SKIP_DALEK5=1" >&2
    exit 1
  fi
  "$here/compare-dalek5.py" --self-test "$here/real-dalek/curve25519-dalek" "$dalek5" \
    "$here/real-x25519/x25519-dalek" "$x25519dalek3" > /dev/null
  echo "the compared items agree apart from the reviewed differences, and the self-test reports every change"
fi

echo "== All checks passed"
