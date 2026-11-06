# curve25519-dalek 5.0.0 through curve25519-dalek-fork

This directory links the track B reference to
[`Beneficial-AI-Foundation/curve25519-dalek-fork`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/tree/95b5831c63ff1c5f6287bd3a77569412a9afdbfb)
(the fork). The fork proves its Aeneas translation of curve25519-dalek 5.0.0, the version in
libsignal, against Lean definitions written by hand. This directory proves the translated
reference equal to the same definitions. The composition gives theorems about that
translation of curve25519-dalek 5.0.0 against the reference, without a second proof of the
dalek code. Section 1 gives the builds that the translation covers.

The theorems refine through a shared model, the fork's `curve25519.x25519`. They do not
step the two programs in lockstep, as tracks A to D do.

All paths are relative to `tracks/fork/`, except the paths that start with `tracks/x25519/`.

## 1. Statement

`lean/ForkSim/X25519.lean`:

- `ForkSim.x25519_scalarmult_spec`: for all 32-byte `k` and `u`, the reference
  `x25519_scalarmult k u` returns bytes whose little-endian value is
  `curve25519.x25519 (k.asNat 8) (u.asNat 8)`.
- `ForkSim.x25519_secret_to_public_spec`: the same for `x25519_secret_to_public k` and
  `curve25519.x25519 (k.asNat 8) 9`.

`lean/ForkSim/Montgomery.lean`:

- `ForkSim.mul_base_clamped_refines`: for every 32-byte `k`,
  `MontgomeryPoint::mul_base_clamped k` returns without panic, overflow or divergence, and
  `x25519_secret_to_public k` returns the same bytes.
- `ForkSim.mul_clamped_refines`: for all 32-byte `u` and `k`, `MontgomeryPoint::mul_clamped u k`
  returns without panic, overflow or divergence, and `x25519_scalarmult k u` returns the same
  bytes.

These statements are about the translated programs, under the assumptions of section 4.

The fork's translation (`scripts/aeneas-translate.sh` in the fork) merges four builds of
curve25519-dalek. Each build uses the Linux target spec `x86_64-unknown-linux-gnu` (64-bit)
or `i686-unknown-linux-gnu` (32-bit). All four use the `serial` backend and the features
`alloc` and `zeroize`. The builds differ by the target and by the feature `precomputed-tables`. A function
with a body per build becomes a dispatch on `get_target`, which returns an opaque string
`target`. The fork's specs hold for every value of `target`. So the two dalek theorems hold
for the four builds. `mul_base_clamped` uses the basepoint table in the two builds with
`precomputed-tables`.

Before the translation, the fork applies the patches in `curve25519-dalek/translation-patches/`
to the source. Three of them change code on the paths of the two functions:

- `montgomery-MontgomeryPoint-mul.patch` replaces the call
  `mul_bits_be(scalar.bits_le().rev().skip(1))` in `Mul<&Scalar> for &MontgomeryPoint`, which
  `mul_clamped` calls, by the body of `mul_bits_be` with a loop over the bit indices 254 to 0.
  It also deletes `Scalar::bits_le`.
- `edwards-EdwardsBasepointTable-mul_base.patch` replaces two `filter` loops with `step_by`
  loops on the table path of `mul_base_clamped`.
- `variable_base-mul.patch` renames a parameter on the path without `precomputed-tables`.

Each of these three patches states that the behavior does not change. Review checks this, not a proof. So the
theorems are about the patched source, and only review links them to the published crate.

Builds outside these four have no theorem here. For example, the default x86_64 build uses
the `simd` backend, or `avx512` when the target enables `avx512ifma` and `avx512vl`
(`build.rs`). Without `precomputed-tables`, such a build can send `mul_base` to AVX2 or
AVX-512 code at run time (`src/backend.rs`, `variable_base_mul`). `mul_clamped` and the table
path do not use this dispatch. aarch64 builds, which the mobile clients of libsignal use,
are not among the four builds either. They select `serial` with 64-bit limbs, so the
translated code is the same as the x86_64 builds, but only a reading of the source shows
this.

The theorems state equality of bytes and termination only. They do not state constant-time
execution, the erasure of secrets, or the check for an all-zero shared secret of RFC 7748,
section 6.1. They do not cover the wrappers of x25519-dalek, such as `PublicKey::from`, or
the calls from libsignal.

## 2. The fork's `x25519` and RFC 7748

The fork defines `x25519 k u = encodeU (montgomery.ladder 255 (clamp k) (decodeU u))` on the
little-endian values of the bytes (`Curve25519/X25519.lean` in the fork). It agrees with
RFC 7748, section 5, on the two points that the RFC leaves to the decoder:

- `clamp k = 2^254 + 8 * (k % 2^254 / 8)`. This clears bits 0, 1, 2 and 255 and sets bit 254,
  as `decodeScalar25519` does.
- `decodeU n = (n % 2^255 : ZMod p)`. This masks bit 255 and reduces modulo `p`, as
  `decodeUCoordinate` does.

The ladder runs over bits 254 to 0, as in the RFC. The reference runs over bits 255 to 0.
Bit 255 is 0 after clamping. For a scalar below `2^255`, `MontgomeryModel.ladder_eq_xMul` of
`EllipticCurve` gives the same result for 255 and for 256 bits
(`ForkSim.ladderXZ_256_eq_255`).

## 3. Translation

`lean/lakefile.toml` requires the fork at commit `95b5831c`. The fork brings its Lean
toolchain (`v4.35.0`), Aeneas (`nightly-2026.10.30-de16f3c`), Mathlib and `EllipticCurve`.

`extract-ref.sh` extracts `tracks/x25519/ref-plain` with the Charon (`0.1.301`) and Aeneas
release that the fork pins. It uses the same entry points as track B. The output
`lean/X25519Ref/Funs.lean` and `lean/X25519Ref/Types.lean` differs from the track B output
only by one added `set_option` line. `ref/` keeps the two Aeneas templates.
`lean/X25519Ref/FunsExternal.lean` and `lean/X25519Ref/TypesExternal.lean` are the track B
field model over `ZMod (2^255 - 19)`, with the same added line.

Track B and its reference stay as they are. Their theorems remain valid for the versions
that they name.

## 4. Assumptions

The trusted base is:

1. For the two reference theorems only: the fork's definitions that they use,
   `curve25519.x25519`, `clamp`, `decodeU`, `encodeU`, `MontgomeryModel.ladder` (from
   `EllipticCurve`) and `Array.asNat`. The fork lists them in `Specs/Montgomery.lean` and asks
   readers to audit `Specs`, `Defs`, `Curve25519` and the definitions of `EllipticCurve`. The
   two dalek theorems do not use these definitions in their statements. They compare the
   dalek program with the reference program directly, so a wrong definition in the fork
   cannot make them say less.
2. Three axioms of the fork, one per Rust crate that it models. Each axiom states that the
   crate's functions meet the fork's contracts for them.
   - `RustAx.core`: `core` (`curve25519-dalek/lean/Curve25519Dalek/FunsExternal.lean`).
   - `RustAx.subtle`: `subtle` (`Subtle/Contract.lean`).
   - `RustAx.zeroize`: `zeroize` (`Zeroize/Contract.lean`).

   The hand-written types of these models are also trusted:
   `curve25519-dalek/lean/Curve25519Dalek/TypesExternal.lean` and `Subtle/Types.lean`.
3. The fork's translation of the dalek source: the translation patches of section 1, Charon
   and Aeneas at the fork's pins, and the configuration of the four builds.
4. The track B field model of the reference (`lean/X25519Ref/FunsExternal.lean`,
   `lean/X25519Ref/TypesExternal.lean`, track B README section 4).
5. The `ref-plain` port of the hacspec spec (track B README section 2).

`lean/Checks/Axioms.lean` checks the axioms with `#guard_msgs`. The two reference theorems
use `propext`, `Classical.choice` and `Quot.sound` only. `mul_base_clamped_refines` adds
`RustAx.core` and `RustAx.subtle`. `mul_clamped_refines` adds `RustAx.core`,
`RustAx.subtle` and `RustAx.zeroize`. The check compares the names of the axioms, not the
contracts that they state. If you move the fork to a new commit, you must read the contracts
again.

## 5. Proof structure

1. `ForkSim/LadderMath.lean` keeps the ladder definitions of the track B file
   `tracks/x25519/lean/Sim/LadderMath.lean`: `lstep`, `ladder` and `enc`.
   `ForkSim/RefSide.lean` comes from the track B file `Sim/RefSide.lean`, with the lemma
   `point_add_and_double_eq` of `Sim/Pilot.lean`. It computes the reference ladder as a pure
   function. Besides the namespace, the port replaces the deprecated `if_true` with
   `ite_true`, and states the literals of the field model with one lemma,
   `fe_lit_eq`.
2. `ForkSim/X25519.lean` reads the bytes of the field model as `Array.asNat 8`, shows that
   `mask_scalar` is the fork's `clamp_integer` (the Lean bodies are the same), and that the
   fork's ladder with its lazy swap is the reference ladder (`toPair_ladderLoop`, from
   `XZ.ladderLoop_eq_foldl` of `EllipticCurve`). The fork states its field as
   `ZMod curve25519.p`, and `transport` moves it to `ZMod (2^255 - 19)`. The extra step at
   bit 255 is `ladderXZ_256_eq_255` (section 2).
3. `ForkSim/Montgomery.lean` composes with the fork's `mul_base_clamped_spec` and
   `mul_clamped_spec`.

## 6. Reproduce

Unpack the Aeneas release `nightly-2026.10.30-de16f3c` into `.aeneas-fork/` at the repository
root, and run `scripts/fetch-upstreams.sh`. Then:

```bash
tracks/fork/extract-ref.sh --check
```

```bash
cd tracks/fork/lean && lake exe cache get && lake build
```

The first build compiles the parts of the fork that the theorems import. On the machine
of this study, it took 2 min 50 s of wall time (23 min of CPU time, peak memory 5.3 GB).
The `.lake` directory takes 8.5 GB, of which Mathlib takes 6.9 GB. The files of this
directory then build in 13 s.
