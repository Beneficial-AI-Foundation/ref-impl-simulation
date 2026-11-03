#!/usr/bin/env bash
# Extracts x25519-dalek 2.0.1 in real-x25519/ with Charon and Aeneas.
#
#   extract-real.sh          write the output to real-x25519/X25519/
#   extract-real.sh --check  extract into a temporary directory. Fail if the output differs
#                            from real-x25519/X25519/
#
# Needs the Aeneas release in .aeneas/ and the Rust toolchain of real-x25519/rust-toolchain.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

# Pins, as in shared/dalek/extract.sh.
charon_version="0.1.281"
aeneas_version="nightly-2026.10.12-d119a47"
workspace="$here/real-x25519"
features="alloc,zeroize,static_secrets"
entry_points=(
  'x25519_dalek::x25519::x25519'
  'x25519_dalek::x25519::StaticSecret::diffie_hellman'
  'x25519_dalek::x25519::SharedSecret::as_bytes'
)
generated=(Funs.lean Types.lean FunsExternal_Template.lean)

mode=${1:-write}
case "$mode" in
  write|--check) ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

export PATH="$root/.aeneas:$PATH"
have=$(charon version | cut -d' ' -f1)
[ "$have" = "$charon_version" ] || { echo "charon $have, expected $charon_version" >&2; exit 1; }
have=$(aeneas -version | cut -d' ' -f2)
[ "$have" = "$aeneas_version" ] || { echo "aeneas $have, expected $aeneas_version" >&2; exit 1; }

start=()
for e in "${entry_points[@]}"; do start+=(--start-from "$e"); done
# The name of the .llbc file gives the Lean module prefix. The path remap makes the
# `Source:` paths relative to the repository root.
(cd "$workspace" && charon cargo --preset=aeneas --dest-file "$tmp/x25519_dalek.llbc" \
  "${start[@]}" -- --locked --offline -p x25519-dalek --no-default-features \
  --features "$features" --config "build.rustflags=[\"--remap-path-prefix=$root/=\"]") \
  > "$tmp/charon.log" 2>&1 || { cat "$tmp/charon.log" >&2; exit 1; }
(cd "$tmp" && aeneas -backend lean -loops-to-rec -split-files -dest X25519 x25519_dalek.llbc) \
  > "$tmp/aeneas.log" 2>&1 || { cat "$tmp/aeneas.log" >&2; exit 1; }

if [ "$mode" = --check ]; then
  for f in "${generated[@]}"; do diff -u "$workspace/X25519/$f" "$tmp/X25519/$f"; done
  echo "the extraction of x25519-dalek gives real-x25519/X25519/"
else
  for f in "${generated[@]}"; do cp "$tmp/X25519/$f" "$workspace/X25519/$f"; done
fi
