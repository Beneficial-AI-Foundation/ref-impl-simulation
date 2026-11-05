#!/usr/bin/env bash
# Extracts curve25519-dalek with Charon and Aeneas for the shared library, and applies the
# hand edits in patches/ and inline-table.py to the clean output.
#
#   extract.sh                write the clean output to extract/ and the patched files to
#                             lean/Curve25519Dalek/
#   extract.sh --check        extract into a temporary directory. Fail if the clean output
#                             differs from extract/ or the patched files differ from lean/
#   extract.sh --check-copies do not run Charon or Aeneas. Apply the hand edits to
#                             extract/ and fail if the result differs from lean/
#
# The first two modes need the Aeneas release in .aeneas/ and the Rust toolchain of
# tracks/x25519/real-dalek/rust-toolchain.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

# Pins.
charon_version="0.1.281"
aeneas_version="nightly-2026.10.12-d119a47"
# The copy of curve25519-dalek 4.2.0 from curve25519-dalek-lean-verify 26d49052, in track B.
# Its .cargo/config.toml selects the serial backend with 64-bit limbs.
workspace="$root/tracks/x25519/real-dalek"
# precomputed-tables gives the basepoint table path of EdwardsPoint::mul_base.
features="alloc,zeroize,precomputed-tables"
# The entry points. Track B uses the first four, track D the next two. The next two are the
# public key path of X25519: mul_base_clamped multiplies the basepoint with the table. The
# last three are the serial variable-base scalar multiplication and two point operations
# that the specs of Curve25519Dalek/Specs/ cover.
entry_points=(
  'crate::montgomery::differential_add_and_double'
  'crate::montgomery::MontgomeryPoint::mul_clamped'
  'crate::montgomery::MontgomeryPoint::to_bytes'
  'crate::montgomery::MontgomeryPoint::as_bytes'
  'crate::ristretto::CompressedRistretto::decompress'
  'crate::ristretto::RistrettoPoint::compress'
  'crate::edwards::EdwardsPoint::mul_base_clamped'
  'crate::edwards::EdwardsPoint::to_montgomery'
  'crate::backend::serial::scalar_mul::variable_base::mul'
  'crate::edwards::EdwardsPoint::double'
  'crate::edwards::EdwardsPoint::as_affine_niels'
)
# All generated files go to extract/. Funs.lean and Types.lean also go to lean/, after the
# patches. lean/ has hand-written files for the items of the two templates.
generated=(Funs.lean Types.lean FunsExternal_Template.lean TypesExternal_Template.lean)
copied=(Funs.lean Types.lean)

mode=${1:-write}
case "$mode" in
  write|--check|--check-copies) ;;
  *) echo "usage: $0 [--check | --check-copies]" >&2; exit 2 ;;
esac

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# apply_patches <dir with clean Funs.lean and Types.lean> <output dir>
# Applies the patches, then inline-table.py. The script rewrites the body of the basepoint
# table into one literal. As a patch, this edit has more than 5,000 lines.
apply_patches() {
  mkdir -p "$2"
  for f in "${copied[@]}"; do cp "$1/$f" "$2/$f"; done
  for p in "$here"/patches/*.patch; do
    patch --quiet --no-backup-if-mismatch -d "$2" -p1 < "$p"
  done
  python3 "$here/inline-table.py" "$2/Funs.lean"
}

if [ "$mode" = --check-copies ]; then
  apply_patches "$here/extract" "$tmp/patched"
  for f in "${copied[@]}"; do diff -u "$here/lean/Curve25519Dalek/$f" "$tmp/patched/$f"; done
  echo "extract/ with the hand edits gives the Lean files of the library"
  exit 0
fi

export PATH="$root/.aeneas:$PATH"
have=$(charon version | cut -d' ' -f1)
[ "$have" = "$charon_version" ] || { echo "charon $have, expected $charon_version" >&2; exit 1; }
have=$(aeneas -version | cut -d' ' -f2)
[ "$have" = "$aeneas_version" ] || { echo "aeneas $have, expected $aeneas_version" >&2; exit 1; }

start=()
for e in "${entry_points[@]}"; do start+=(--start-from "$e"); done
# The name of the .llbc file gives the Lean module prefix, Curve25519Dalek.
(cd "$workspace" && charon cargo --preset=aeneas --dest-file "$tmp/curve25519_dalek.llbc" \
  "${start[@]}" -- --locked --offline -p curve25519-dalek --no-default-features \
  --features "$features") > "$tmp/charon.log" 2>&1 \
  || { cat "$tmp/charon.log" >&2; exit 1; }
(cd "$tmp" && aeneas -backend lean -loops-to-rec -split-files -dest out curve25519_dalek.llbc) \
  > "$tmp/aeneas.log" 2>&1 || { cat "$tmp/aeneas.log" >&2; exit 1; }
apply_patches "$tmp/out" "$tmp/patched"

if [ "$mode" = --check ]; then
  for f in "${generated[@]}"; do diff -u "$here/extract/$f" "$tmp/out/$f"; done
  for f in "${copied[@]}"; do diff -u "$here/lean/Curve25519Dalek/$f" "$tmp/patched/$f"; done
  echo "the extraction replays, and the hand edits give the Lean files of the library"
else
  mkdir -p "$here/extract"
  for f in "${generated[@]}"; do cp "$tmp/out/$f" "$here/extract/$f"; done
  for f in "${copied[@]}"; do cp "$tmp/patched/$f" "$here/lean/Curve25519Dalek/$f"; done
  echo "wrote extract/ and lean/Curve25519Dalek/Funs.lean and Types.lean"
fi
