#!/usr/bin/env bash
# Extracts the track B reference crate (tracks/x25519/ref-plain) with the Charon and Aeneas
# release that curve25519-dalek-fork pins.
#
#   extract-ref.sh          write the output to ref/ and lean/X25519Ref/
#   extract-ref.sh --check  extract into a temporary directory. Fail if the output differs
#
# Needs the Aeneas release nightly-2026.10.30-de16f3c in .aeneas-fork/ at the repository root,
# the Rust toolchain of ref-plain/rust-toolchain, and tracks/x25519/hacspec-old
# (scripts/fetch-upstreams.sh).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

charon_version="0.1.301"
aeneas_version="nightly-2026.10.30-de16f3c"
crate="$root/tracks/x25519/ref-plain"
# Aeneas output: Funs.lean and Types.lean are used as they are. The two templates are kept in
# ref/ to compare with the hand-written lean/X25519Ref/{Funs,Types}External.lean.
used=(Funs.lean Types.lean)
templates=(FunsExternal_Template.lean TypesExternal_Template.lean)

mode=${1:-write}
case "$mode" in
  write|--check) ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

export PATH="$root/.aeneas-fork:$PATH"
have=$(charon version | cut -d' ' -f1)
[ "$have" = "$charon_version" ] || { echo "charon $have, expected $charon_version" >&2; exit 1; }
have=$(aeneas -version | cut -d' ' -f2)
[ "$have" = "$aeneas_version" ] || { echo "aeneas $have, expected $aeneas_version" >&2; exit 1; }

(cd "$crate" && charon cargo --preset=aeneas --dest-file "$tmp/x25519_ref.llbc" \
  --start-from crate::x25519_scalarmult --start-from crate::x25519_secret_to_public \
  --start-from crate::point_add_and_double --start-from crate::x25519_is_all_zero \
  --opaque crate::field) > "$tmp/charon.log" 2>&1 || { cat "$tmp/charon.log" >&2; exit 1; }
(cd "$tmp" && aeneas -backend lean -split-files -loops-to-rec -namespace x25519_ref \
  -dest X25519Ref x25519_ref.llbc) > "$tmp/aeneas.log" 2>&1 || { cat "$tmp/aeneas.log" >&2; exit 1; }

if [ "$mode" = --check ]; then
  for f in "${used[@]}"; do diff -u "$here/lean/X25519Ref/$f" "$tmp/X25519Ref/$f"; done
  for f in "${templates[@]}"; do diff -u "$here/ref/$f" "$tmp/X25519Ref/$f"; done
  echo "the extraction of ref-plain gives lean/X25519Ref/ and ref/"
else
  mkdir -p "$here/lean/X25519Ref" "$here/ref"
  for f in "${used[@]}"; do cp "$tmp/X25519Ref/$f" "$here/lean/X25519Ref/$f"; done
  for f in "${templates[@]}"; do cp "$tmp/X25519Ref/$f" "$here/ref/$f"; done
fi
