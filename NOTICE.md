# Third-party code

This repository contains work copies of third-party code, so that every extraction can be
run again. Each copy keeps the license of its source. The table lists each copy, its
source, the commit, the license and the edits made in this repository.

| Directory | Source | Commit | License | Edits |
|---|---|---|---|---|
| `tracks/chacha20poly1305/real/` | `cryspen/libcrux`, crates `chacha20poly1305`, `poly1305`, `hacl-rs`, `macros`, `secrets`, `traits` | `3ade18381ad3144d755507f97994933d8585839b` | Apache-2.0 (`LICENSE`) | A root `Cargo.toml`, 5 manifest lines and a `rust-toolchain`. 52 lines in `poly1305/src/hacl/mac_poly1305.rs` (section 2 of the track README) |
| `tracks/chacha20poly1305/ref-hax/` | `cryspen/hax`, `examples/chacha20` | `a1ddcfffd617a9f29442acb900a01df7339f3ea8` | Apache-2.0 (`LICENSE`) | 33 lines in `src/lib.rs`, and the manifest |
| `tracks/chacha20poly1305/ref-hacspec/` | `hacspec/hacspec`, `lib/`, `utils/`, `examples/` | `4ecc847fc944fe996e19423aa41f002f2039dab0` | MIT (`LICENSE`). The crate manifests say MIT OR Apache-2.0 | 1 line, and the manifests |
| `tracks/hpke/real-work/` | `cryspen/hpke-rs` 0.6.1 | `e1a4b12d3e630c713a89e97a2a91e4a597f3fc82` | MPL-2.0 (manifest). `LICENSE` holds the MPL-2.0 text, added here | 1 line in `src/kdf.rs` |
| `tracks/x25519/real-dalek/curve25519-dalek/` | curve25519-dalek 4.2.0 as modified by `Beneficial-AI-Foundation/curve25519-dalek-lean-verify` | `26d49052347e52cb3923952ea225d28faf48fe72` | BSD-3-Clause (`LICENSE`) | None in this repository |
| `tracks/x25519/real-x25519/x25519-dalek/` | x25519-dalek 2.0.1 from crates.io, `dalek-cryptography/curve25519-dalek`, `x25519-dalek/` | `4ac84dd0668b1d2e51654fcdffe4ae6a687bef00` | BSD-3-Clause (`LICENSE`) | None. A root `Cargo.toml` outside the copy points its curve25519-dalek dependency to `tracks/x25519/real-dalek/curve25519-dalek/` |
| `shared/dalek/lean/Curve25519Dalek/` (`Auxiliary.lean`, `Math/`, `Specs/`) | `curve25519-dalek-lean-verify` | `26d49052347e52cb3923952ea225d28faf48fe72` | Apache-2.0 (`LICENSE`) | Ported to Aeneas `d119a474`. Each file with changes to its definitions, statements or proofs has a "Port note" in its header. The docstrings of the files ported with the point specs are rewritten. `Specs/.../CarryBlock.lean` is new. `Specs/.../Negate.lean` is unchanged. The point specs in `Specs/Backend/Serial/CurveModels/`, `Specs/Edwards/EdwardsPoint/` and `Specs/Window/LookupTable/`, the field specs `ConditionalAssign`, `ConditionalSelect`, `FromLimbs`, `Neg`, `ONE`, `Square2`, `ZERO` and `Constants/EdwardsD2`, and `Math/Edwards/Representation.lean` are ported from the same commit. The point specs state the points in the group of `DalekSim/Edwards.lean`. `Specs/Window/Basic.lean` copies `next_spec` and an `Inhabited` instance from two upstream files. `Specs/Axioms.lean` is new. `Math/Edwards/Curve.lean` keeps the curve parameters of the upstream file and replaces its point type with that group. `Specs/Subtle.lean` holds the `subtle` spec theorems of the upstream `FunsExternal.lean`. `FunsExternal.lean` and `TypesExternal.lean` are Aeneas templates filled with 6 definitions copied from `curve25519-dalek-lean-verify` and 7 definitions written for track D. `conditional_swap` is changed to call `conditional_assign`, as the Rust default method does |
| `tracks/x25519/ref-hacspec/` | `hacspec/specs`, `curve25519` | `c511110d6f4bb4628da193a2c8e44c928d9555b8` | Apache-2.0 (`LICENSE`) | The manifest and a `rust-toolchain`. `src/curve25519.rs` is renamed to `src/lib.rs`, with its text unchanged. Tests and benchmarks are not copied |
| `tracks/x25519/ref-plain/` | A port to plain Rust of `hacspec/specs` `curve25519` | `c511110d6f4bb4628da193a2c8e44c928d9555b8` | Apache-2.0 (`LICENSE`) | The port itself (track B README, section 2) |
| `tracks/ristretto/ref-plain/` | A port to plain Rust of `hacspec/specs` `ristretto`, and of `point_add`, `point_identity` and `point_mul` of `hacspec/specs` `edwards25519` | `c511110d6f4bb4628da193a2c8e44c928d9555b8` | Apache-2.0 (`LICENSE`) | The port itself (track D README, section 2) |

`cryspen/hpke-spec` (`85429a9ab519ca6eb5b286294203cefe75399223`), the reference of track C,
has no license. This repository does not include a copy of it.
`scripts/fetch-upstreams.sh` clones it, and `tracks/hpke/make-ref-shim.sh` builds the work
tree `tracks/hpke/ref-shim/` from the clone and `tracks/hpke/patches/hpke-spec.patch`. The
patch changes the manifests and the root toolchain file, removes the 5 per-crate toolchain
files and adds a lockfile.

The other upstream repositories that the tracks use are cloned by
`scripts/fetch-upstreams.sh` and are not part of this repository.

The Lean files that Aeneas generated are translations of the code in the table and of
hpke-spec. They are in `Ref/`, `Real/`, `RealAead/`, `X25519Ref/`, `RistrettoRef/`,
`shared/dalek/extract/`, `real-x25519/X25519/` and `ref-plain/Ref/`. They are also `Curve25519Dalek/Funs.lean`,
`Curve25519Dalek/Types.lean`, `X25519Dalek/Funs.lean` and `X25519Dalek/Types.lean`.
`shared/dalek/patches/` and `shared/dalek/inline-table.py` hold the hand edits of
`Curve25519Dalek/Funs.lean`.
