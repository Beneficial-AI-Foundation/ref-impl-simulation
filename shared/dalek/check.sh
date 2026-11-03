#!/usr/bin/env bash
# Runs the checks of the shared curve25519-dalek library and stops at the first failure.
# Tracks B and D run it before their own checks. Set REPLAY_EXTRACTION=1 to also run Charon
# and Aeneas again and compare their output with extract/.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root="$here/../.."

echo "== Shared library: the Lean files are the Aeneas output with the patches"
if [ "${REPLAY_EXTRACTION:-0}" = 1 ]; then
  "$here/extract.sh" --check
else
  "$here/extract.sh" --check-copies
fi

echo "== Shared library: Lean build"
(cd "$here/lean" && lake build)

echo "== Shared library: name-binding check"
(cd "$here/lean" && "$root/scripts/check-short-names.py" Curve25519Dalek/*.lean)
