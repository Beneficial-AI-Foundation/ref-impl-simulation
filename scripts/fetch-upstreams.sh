#!/usr/bin/env bash
# Re-create what .gitignore excludes: the upstream clones at the recorded commits, the
# track C reference tree built from hpke-spec, and the copies of the Aeneas Lean backend.
# Run from the repository root, after unpacking the Aeneas release into .aeneas/.
set -euo pipefail
clone() { # dir url commit
  [ -d "$1/.git" ] || git clone -q "$2" "$1"
  git -C "$1" checkout -q "$3"
}
clone tracks/hpke/hacspec    https://github.com/hacspec/hacspec.git  4ecc847fc944fe996e19423aa41f002f2039dab0
clone tracks/hpke/hpke-spec  https://github.com/cryspen/hpke-spec.git 85429a9ab519ca6eb5b286294203cefe75399223
clone tracks/hpke/hpke-rs    https://github.com/cryspen/hpke-rs.git   e1a4b12d3e630c713a89e97a2a91e4a597f3fc82
clone tracks/chacha20poly1305/upstream/hacspec https://github.com/hacspec/hacspec.git 4ecc847fc944fe996e19423aa41f002f2039dab0
clone tracks/chacha20poly1305/upstream/hax     https://github.com/cryspen/hax.git     a1ddcfffd617a9f29442acb900a01df7339f3ea8
clone tracks/x25519/hacspec-specs  https://github.com/hacspec/specs.git           c511110d6f4bb4628da193a2c8e44c928d9555b8
clone tracks/x25519/hacspec-old    https://github.com/hacspec/hacspec.git         4ecc847fc944fe996e19423aa41f002f2039dab0
clone tracks/x25519/aeneas-src     https://github.com/AeneasVerif/aeneas.git      d119a474f852781f8ae88a85424f2f8ba8407b82
# Track D uses the track B clones of hacspec-specs and hacspec-old.
# The shared curve25519-dalek library of tracks B and D.
clone shared/dalek/lean/primecert  https://github.com/b-mehta/PrimeCert.git       f699a3e5d3efb381b9ddfb61a1ca51be25f456bd
# tracks/fork requires curve25519-dalek-fork as a Lake package, so `lake build` fetches it:
# https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork.git at
# 95b5831c63ff1c5f6287bd3a77569412a9afdbfb (tracks/fork/lean/lakefile.toml).
# tracks/fork/extract-ref.sh and tracks/fork/extract-ristretto-ref.sh need the Aeneas release
# nightly-2026.10.30-de16f3c in .aeneas-fork/.

# Track C: hpke-spec has no license, so the patched tree is built here, not committed.
tracks/hpke/make-ref-shim.sh

# Each Lean project requires the Aeneas Lean library from lean/aeneas-backend. Tracks B and D
# get it, with PrimeCert and Mathlib, from the shared library.
for d in tracks/chacha20poly1305/lean tracks/hpke/lean shared/dalek/lean; do
  [ -d "$d/aeneas-backend" ] || cp -r .aeneas/backends/lean "$d/aeneas-backend"
done
