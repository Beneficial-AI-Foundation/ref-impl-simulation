# Shared library: curve25519-dalek in Lean

This directory holds one Aeneas extraction of curve25519-dalek and the Lean library built on
it. Track B ([`tracks/x25519`](../../tracks/x25519/README.md)) and track D
([`tracks/ristretto`](../../tracks/ristretto/README.md)) import the library. Their proofs
about the real code use the same Lean definitions.

All paths are relative to `shared/dalek/`.

## 1. Extraction

`extract.sh` runs Charon and Aeneas and applies the hand edits. The script holds the pins:

| Item | Value |
|---|---|
| Rust code | the copy of curve25519-dalek 4.2.0 from `curve25519-dalek-lean-verify` `26d49052`, in `../../tracks/x25519/real-dalek/curve25519-dalek` |
| Backend | serial, 64-bit limbs (`../../tracks/x25519/real-dalek/.cargo/config.toml`) |
| Features | `--no-default-features --features alloc,zeroize` |
| Charon | `0.1.281` |
| Aeneas | `nightly-2026.10.12-d119a47` |
| Rust | `nightly-2026-09-17` (`../../tracks/x25519/real-dalek/rust-toolchain`) |

Charon starts from six functions. Track B uses the first four, and track D uses the last
two:

1. `montgomery::differential_add_and_double`
2. `montgomery::MontgomeryPoint::mul_clamped`
3. `montgomery::MontgomeryPoint::to_bytes`
4. `montgomery::MontgomeryPoint::as_bytes`
5. `ristretto::CompressedRistretto::decompress`
6. `ristretto::RistrettoPoint::compress`

The script writes the clean Aeneas output to `extract/`. It copies `Funs.lean` and
`Types.lean` to `lean/Curve25519Dalek/` and applies the patches in `patches/` to the
copies. There is one patch, `01-mul-scalar-shadowing.patch`. Its header gives the reason.

The output has 55 functions and constants and 7 type and trait declarations. Each of them
except `MontgomeryPoint::as_bytes` is also in the earlier extraction of track B or of track
D, with the same text. `as_bytes` came later, for `SharedSecret::as_bytes` in track B. Its
Lean body is `ok self`. The two templates list 11 external
functions and the external type `subtle.Choice`.

Commands, from the repository root, with the Aeneas release in `.aeneas/`:

```bash
shared/dalek/extract.sh
```

```bash
shared/dalek/extract.sh --check
```

The first command writes `extract/` and the two Lean files. The second command extracts
into a temporary directory and compares the result with the committed files. If they
differ, it fails.
`extract.sh --check-copies` runs neither Charon nor Aeneas. It applies the patches to
`extract/` and compares the result with `lean/`.

## 2. Lean library

`lean/` is a Lake package named `dalek` with two libraries. The first is `Curve25519Dalek`:

| File | Source |
|---|---|
| `Funs.lean`, `Types.lean` | `extract/`, with the patches |
| `FunsExternal.lean` | hand-written definitions of the 11 external functions of `subtle` and `zeroize`: 5 from track B and 6 from track D, plus the loop of the slice `ct_eq` from track D (the READMEs of the tracks, section 4) |
| `TypesExternal.lean` | the type `subtle.Choice`, from `curve25519-dalek-lean-verify` |
| `Math/`, `Auxiliary.lean` | `curve25519-dalek-lean-verify` `26d49052` |
| `Specs/` | the field specs. Track B ported them to Aeneas `d119a474` (track B README, section 2). `Negate.lean` comes from track D and is unchanged from `curve25519-dalek-lean-verify` |

No definition in `FunsExternal.lean` is an axiom. The library does not contain the
relations to the reference programs or the refinement proofs. Those use the field model of
each reference and stay in the `Sim/` directory of each track.

The second library, `DalekSim` (`lean/DalekSim/`), holds the lemmas of the proofs that do
not depend on a reference, in the namespace `DalekSim`:

| File | Content |
|---|---|
| `Bytes.lean` | `U8x32_as_Nat` as base-256 digits (`digits_lt`, `digits_get`, `U8x32_as_Nat_eq`, `byte_lt`, `U8x32_digit`), Horner's rule (`foldr_horner`), clearing bit 255 (`U8x32_mask_top`), the injectivity of `U8x32_as_Nat` (`U8x32_inj`), the value 0 (`U8x32_zero`, `U8x32_eq_zero_iff`) and bytes from digits (`U8x32_of_digits`) |
| `Basic.lean` | the limb bound `Bnd` and `bnd_mono`, and the `Result` lemmas `exists_ok_of_spec` and `eq_ok_of_spec` |
| `Choice.lean` | the slice `ct_eq` of `subtle` on two 32-byte arrays (`ct_eq_loop_u8`, `slice_ct_eq_arr`), and `to_bytes` and the field `ct_eq` over `Field51_as_Nat` mod `p` (`to_bytes_mod`, `fe_ct_eq_mod`). Track D wrote the slice lemmas. Both tracks use them |
| `Edwards.lean` | the group law of the Edwards curve `-x² + y² = 1 + d x² y²` over a field where `2 ≠ 0`, `-1` is a square and `d` is not (class `Complete`): the denominators of the unified addition are never 0, the sum is on the curve, associativity (`add_assoc'`), the group `Point d` with `nsmul` lemmas for a ladder, and the instance for edwards25519. `dEd` is the parameter `d` as an element of `ZMod p`, with `dEd_not_square` and `dEd_rel` (`121666 d = -121665`), which track B uses in `Sim/EdwardsBridge.lean`. The certificates of the polynomial identities come from Singular, through `tools/edwards-assoc/gen.py`. `linear_combination` checks them, so the script is not trusted |

Tracks B and D open the namespace `DalekSim` in their proofs.

The package requires Aeneas from `lean/aeneas-backend` and PrimeCert from `lean/primecert`.
`scripts/fetch-upstreams.sh` creates both. The two tracks require `dalek` and get Aeneas
and PrimeCert through it. Their lakefiles also set `packagesDir` to
`lean/.lake/packages`, so the library and the two tracks use one copy of Mathlib and of
the other packages. Thus a build of either track writes to the same build directories.
`check.sh` of each track takes a lock (`flock`) on `lean/.lake/check.lock`, so that two
checks do not build at the same time. If `flock` is not installed, the script stops with an
error. `shared/dalek/check.sh` takes no lock, because the tracks call it while they hold
the lock. If you run it, or `lake build`, by hand, do not run a check of a track at the same
time.

## 3. Checks

`check.sh` runs `extract.sh --check-copies`, `lake build` in `lean/` and
`scripts/check-short-names.py` on `lean/Curve25519Dalek/*.lean`. With
`REPLAY_EXTRACTION=1`, it runs `extract.sh --check` in place of `--check-copies`. The
`check.sh` of track B and of track D run it first.
