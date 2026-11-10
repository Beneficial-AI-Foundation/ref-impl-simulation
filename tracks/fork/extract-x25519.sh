#!/usr/bin/env bash
# Extracts x25519-dalek 3.0.0 with the Charon and Aeneas release that curve25519-dalek-fork
# pins. The source is the fork's x25519-dalek/ at the commit in lean/lakefile.toml.
#
#   extract-x25519.sh          write the output to x25519/ and lean/X25519Dalek/
#   extract-x25519.sh --check  extract into a temporary directory. Fail if the output differs
#
# Needs the Aeneas release nightly-2026.10.30-de16f3c in .aeneas-fork/ at the repository root,
# its Rust toolchain, and the fork in lean/.lake/packages/curve25519-dalek (run `lake build`
# or `lake update` in lean/ first).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

charon_version="0.1.301"
aeneas_version="nightly-2026.10.30-de16f3c"
fork="$here/lean/.lake/packages/curve25519-dalek"
fork_rev=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2}
  /^rev = / && name=="curve25519-dalek"{print $2}' "$here/lean/lakefile.toml")
# The crate on crates.io, as libsignal fc90b90f locks it in Cargo.lock.
crate_sha256="e7e8131a03190127fb2263afc72b322ecadae46b6ff8c6f399ff5d02f5559af6"
# libsignal fc90b90f uses the default features (`precomputed-tables`, `zeroize`) and
# `static_secrets` (rust/core). We add `reusable_secrets`. `precomputed-tables` is set per build
# below, as the fork does.
features="zeroize,static_secrets,reusable_secrets"
# Charon's --start-from does not accept trait impls with generics, such as the From impls. So
# the extraction starts from the whole module. It excludes `Debug` and `Hash`, because the fork
# has no model of `core::fmt` or of the `Hash` impl of `MontgomeryPoint`.
entry_points=('x25519_dalek::x25519')
excluded=(
  '{impl core::fmt::Debug for x25519_dalek::x25519::_}'
  '{impl core::hash::Hash for x25519_dalek::x25519::_}'
)
generated=(Funs.lean Types.lean)
templates=(FunsExternal_Template.lean TypesExternal_Template.lean)

mode=${1:-write}
case "$mode" in
  write|--check) ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

export PATH="$root/.aeneas-fork:$PATH"
have=$(charon version | cut -d' ' -f1)
[ "$have" = "$charon_version" ] || { echo "charon $have, expected $charon_version" >&2; exit 1; }
have=$(aeneas -version | cut -d' ' -f2)
[ "$have" = "$aeneas_version" ] || { echo "aeneas $have, expected $aeneas_version" >&2; exit 1; }
have=$(git -C "$fork" rev-parse HEAD)
[ "$have" = "$fork_rev" ] || { echo "fork at $have, expected $fork_rev" >&2; exit 1; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# The fork's Cargo workspace at the pinned commit, with its translation patches, as in its
# scripts/aeneas-translate.sh. `git archive` reads the commit, not the working tree. So local
# edits and ignored files, for example a `.cargo/config.toml`, do not reach the build.
work="$tmp/work"
mkdir "$work"
git -C "$fork" archive "$fork_rev" Cargo.toml Cargo.lock curve25519-dalek \
  curve25519-dalek-derive ed25519-dalek x25519-dalek | tar -x -C "$work"
rm -rf "$work/curve25519-dalek/lean"
for patch in "$work"/curve25519-dalek/translation-patches/*.patch; do
  (cd "$work" && GIT_CEILING_DIRECTORIES="$tmp" git apply "$patch")
done

# If cargo has the crate in its cache, check that its source equals the fork's copy at the commit.
crate=$(ls "${CARGO_HOME:-$HOME/.cargo}"/registry/cache/*/x25519-dalek-3.0.0.crate 2>/dev/null \
  | head -1 || true)
if [ -n "$crate" ]; then
  [ "$(sha256sum "$crate" | cut -d' ' -f1)" = "$crate_sha256" ] \
    || { echo "$crate: wrong checksum" >&2; exit 1; }
  mkdir "$tmp/crate" && tar xzf "$crate" -C "$tmp/crate"
  diff -r "$tmp/crate/x25519-dalek-3.0.0/src" "$work/x25519-dalek/src" \
    || { echo "the fork's x25519-dalek/src differs from crates.io 3.0.0" >&2; exit 1; }
else
  echo "x25519-dalek-3.0.0.crate is not in the cargo cache: the check against crates.io is skipped" >&2
fi

start=()
for e in "${entry_points[@]}"; do start+=(--start-from "$e"); done
for e in "${excluded[@]}"; do start+=(--exclude "$e"); done
# Only x25519-dalek is translated. Its calls into curve25519-dalek, subtle and zeroize stay
# opaque, and lean/X25519Dalek/FunsExternal.lean points them to the fork's definitions.
# The path remap makes the `Source:` paths relative to the workspace.
# The four builds of the fork, merged by Charon as in the fork's script: 64-bit and 32-bit, each
# with and without `precomputed-tables`. Items whose bodies differ by build dispatch on
# `get_target`, as in the fork's translation.
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
rustc="$(charon toolchain-path)/bin/rustc"
serial='--cfg curve25519_dalek_backend="serial"'
remap="--remap-path-prefix=$work/="
targets=()
for arch in x86_64 i686; do
  for spec in "$arch-tables" "$arch-no-tables"; do
    "$rustc" -Z unstable-options --print target-spec-json --target "$arch-unknown-linux-gnu" \
      > "$tmp/$spec.json"
    targets+=(--targets "$tmp/$spec.json")
  done
  tables='--cfg feature="precomputed-tables"'
  export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$arch-tables")_RUSTFLAGS=$serial $tables $remap"
  export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$arch-no-tables")_RUSTFLAGS=$serial $remap"
done
(cd "$work/x25519-dalek" && charon cargo --preset=aeneas "${targets[@]}" \
  --dest-file "$tmp/x25519_dalek.llbc" "${start[@]}" \
  -- --locked --no-default-features --features "$features" \
  -Zjson-target-spec -Zbuild-std=core,alloc) \
  > "$tmp/charon.log" 2>&1 || { cat "$tmp/charon.log" >&2; exit 1; }
(cd "$tmp" && aeneas -backend lean -split-files -loops-to-rec -max-heartbeats 200000 \
  -namespace x25519_dalek -dest X25519Dalek x25519_dalek.llbc) \
  > "$tmp/aeneas.log" 2>&1 || { cat "$tmp/aeneas.log" >&2; exit 1; }

if [ "$mode" = --check ]; then
  for f in "${generated[@]}"; do diff -u "$here/lean/X25519Dalek/$f" "$tmp/X25519Dalek/$f"; done
  for f in "${templates[@]}"; do diff -u "$here/x25519/$f" "$tmp/X25519Dalek/$f"; done
  echo "the extraction of x25519-dalek 3.0.0 gives lean/X25519Dalek/ and x25519/"
else
  mkdir -p "$here/lean/X25519Dalek" "$here/x25519"
  for f in "${generated[@]}"; do cp "$tmp/X25519Dalek/$f" "$here/lean/X25519Dalek/$f"; done
  for f in "${templates[@]}"; do cp "$tmp/X25519Dalek/$f" "$here/x25519/$f"; done
fi
