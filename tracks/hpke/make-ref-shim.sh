#!/usr/bin/env bash
# Build ref-shim/ from the hpke-spec clone and patches/hpke-spec.patch.
# hpke-spec has no license, so this repository does not include a copy of it.
# Run scripts/fetch-upstreams.sh first: it clones hpke-spec into hpke-spec/.
# The patch points the spec crates at the shims in shim/ and pins the toolchain.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd)
rm -rf "$T/ref-shim"
mkdir "$T/ref-shim"
for f in aead errors hpke kdf kem Cargo.toml Readme.md doc.sh test_and_check.sh rust-toolchain; do
  cp -r "$T/hpke-spec/$f" "$T/ref-shim/"
done
(cd "$T/ref-shim" && patch -s -p1 < "$T/patches/hpke-spec.patch")
