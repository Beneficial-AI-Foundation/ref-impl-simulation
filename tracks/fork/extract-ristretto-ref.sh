#!/usr/bin/env bash
# Extracts the track D reference crate (tracks/ristretto/ref-plain) with the Charon and Aeneas
# release that curve25519-dalek-fork pins.
#
#   extract-ristretto-ref.sh          write the output to ref-ristretto/ and lean/RistrettoRef/
#   extract-ristretto-ref.sh --check  extract into a temporary directory. Fail if the output differs
#
# Needs the Aeneas release nightly-2026.10.30-de16f3c in .aeneas-fork/ at the repository root,
# the Rust toolchain of ref-plain/rust-toolchain, tracks/x25519/hacspec-old and
# tracks/x25519/hacspec-specs (scripts/fetch-upstreams.sh), and curve25519-dalek 5.0.0 in the
# cargo registry (a dev-dependency of ref-plain).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

charon_version="0.1.301"
aeneas_version="nightly-2026.10.30-de16f3c"
crate="$root/tracks/ristretto/ref-plain"
# Aeneas output: Funs.lean and Types.lean are used as they are. The two templates are kept in
# ref-ristretto/ to compare with the hand-written lean/RistrettoRef/{Funs,Types}External.lean.
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

(cd "$crate" && charon cargo --preset=aeneas --dest-file "$tmp/ristretto_ref.llbc" \
  --start-from crate::decode --start-from crate::encode --start-from crate::edwards::point_mul \
  --opaque crate::field --opaque crate::scalar -- --offline) > "$tmp/charon.log" 2>&1 ||
  { cat "$tmp/charon.log" >&2; exit 1; }
(cd "$tmp" && aeneas -backend lean -split-files -loops-to-rec -max-heartbeats 200000 \
  -namespace ristretto_ref -dest RistrettoRef ristretto_ref.llbc) > "$tmp/aeneas.log" 2>&1 ||
  { cat "$tmp/aeneas.log" >&2; exit 1; }

if [ "$mode" = --check ]; then
  for f in "${used[@]}"; do diff -u "$here/lean/RistrettoRef/$f" "$tmp/RistrettoRef/$f"; done
  for f in "${templates[@]}"; do diff -u "$here/ref-ristretto/$f" "$tmp/RistrettoRef/$f"; done
  echo "the extraction of ref-plain gives lean/RistrettoRef/ and ref-ristretto/"
else
  mkdir -p "$here/lean/RistrettoRef" "$here/ref-ristretto"
  for f in "${used[@]}"; do cp "$tmp/RistrettoRef/$f" "$here/lean/RistrettoRef/$f"; done
  for f in "${templates[@]}"; do cp "$tmp/RistrettoRef/$f" "$here/ref-ristretto/$f"; done
fi
