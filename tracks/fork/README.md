# curve25519-dalek 5.0.0 through curve25519-dalek-fork

This directory links the track B reference to
[`Beneficial-AI-Foundation/curve25519-dalek-fork`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/tree/95b5831c63ff1c5f6287bd3a77569412a9afdbfb)
(the fork). The fork proves its Aeneas translation of curve25519-dalek 5.0.0, the version in
libsignal, against Lean definitions written by hand. This directory proves the translated
reference equal to the same definitions. The composition gives theorems about that
translation of curve25519-dalek 5.0.0 against the reference, without a second proof of the
dalek code. Section 1 gives the builds that the translation covers. Sections 1 to 6 are about
X25519 (track B). Section 7 does the same for Ristretto (track D).

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

## 7. Ristretto (track D)

This section links the track D reference (`tracks/ristretto/ref-plain`, RFC 9496) to the
fork's Ristretto specs. All four builds of section 1 are covered. The fork has one
`decompress`, `compress` and `mul` per build, so each dalek theorem below has four copies,
in the namespaces `ForkRistretto.«x86_64-tables»`, `«i686-tables»`, `«x86_64-no-tables»` and
`«i686-no-tables»`. The limb bound `n` is 52 on x86_64 and 26 on i686.

### 7.1 Statement

The reference theorems (`lean/ForkRistretto/`) compare the reference with the fork's
definitions. The fork computes in `ZMod curve25519.p` and the reference in `field.Fe`, which
is `ZMod (2 ^ 255 - 19)`. `toF` is the ring isomorphism between the two.

- `ForkRistretto.decode_spec` (`Encoding.lean`): for every 32-byte `b`, the reference
  `decode b` returns a result `q` with `DecRel q (Ristretto.decodeRep (b.asNat 8))`. So `decode`
  returns the error `20` exactly when the fork's `decodeRep` returns `none`. Otherwise it
  returns `refOf P = (x, y, 1, x y)` for the point `P = (x, y)` of `decodeRep`.
- `ForkRistretto.encode_spec` (`Encoding.lean`): if `Q = (X, Y, Z, T)` represents a point `P`
  (`Rep Q P`: `Z ≠ 0`, `X Y = Z T`, `P = (X / Z, Y / Z)`), the reference `encode Q` returns
  bytes whose value is `Ristretto.encodeRep P`. `P` is any point of the curve, so the theorem
  holds for every valid representative, not only for even points.
- `ForkRistretto.point_mul_spec` (`ScalarMul.lean`): if `Rep Q P`, the reference
  `edwards.point_mul s Q` returns a representative of `scVal s • P` in the fork's group
  `curve25519.edwards.Point`. `scVal s` is the representative below `l` of `s : ZMod l`. The
  group has order `8 l`, so `s` itself does not act on it.
  `point_mul_spec_of` gives `k • P` for a natural number `k` with `(k : ZMod l) = s`, if
  `k < l` or `l • P = 0`. `point_mul_encode_spec` gives the encoding of `k • P` with no
  premise on `k`, if `P` is even.

The dalek theorems (`lean/ForkRistretto/Dalek.lean`), for each build:

- `decompress_refines`: for every 32-byte input, `CompressedRistretto::decompress` returns
  without panic, overflow or divergence. The reference `decode` returns a result `q` with
  `DecRel q (r.map toPoint)`, for the dalek result `r`. So both reject the same inputs. On the
  other inputs, the reference returns `(x, y, 1, x y)` for the point `(x, y)` that the dalek
  result represents. The theorem also keeps the fork's facts on a returned point: it is on the
  curve, even, and has `LimbsLt n`. So its result meets the premises of the next theorems.
- `compress_refines`: for a point `P` with `P.LimbsLt n` and `P.OnCurve`,
  `RistrettoPoint::compress` returns the bytes of the reference `encode (extRef P.toExtended)`.
  `extRef` reads the four coordinates of the dalek point as reference field elements.
- `mul_refines`: for a point `P` as above, a dalek scalar `k` with `k.asNat < 2 ^ 255`, and a
  reference scalar `s` with `(k.asNat : ZMod l) = s`, `Mul<&Scalar> for &RistrettoPoint`
  returns a point `r`. The result `r` is on the curve, has `LimbsLt n`, and is even if `P` is
  even. If moreover `k.asNat < l` or `l • P.toPoint = 0`, the reference
  `point_mul s (extRef P.toExtended)` returns a representative of `r.toPoint`. This condition
  is inside the postcondition, so the facts on `r` hold for every `k` below `2 ^ 255`.
- `mul_compress_refines`: with `P`, `k` and `s` as above, if `P.toPoint` is also even (a
  Ristretto representative), and `Q`
  is any reference representative of `P.toPoint`, `compress` of the dalek product returns the
  bytes of the reference `encode (point_mul s Q)`. No premise `k < l` is needed (section 7.4).
- `decompress_mul_compress_refines`: the three steps together. If `decompress` returns
  `none`, the reference `decode` returns the error `20`. If it returns a point `P`, the
  reference `decode` returns `Ok q`, and `compress` of `P * k` returns the bytes of the
  reference `encode (point_mul s q)`. Its premises are only `k.asNat < 2 ^ 255` and
  `(k.asNat : ZMod l) = s`.
- `from_bytes_decompress_mul_compress_refines`: the same, end to end from two byte arrays. The
  dalek scalar is `Scalar::from_bytes_mod_order sb`, and the reference scalar is
  `s = sb.asNat 8` in `ZMod l`, which is what the reference `sc_from_bytes` computes. The
  premise `(sb.asNat 8 : ZMod l) = s` only names `s`. The fork's `from_bytes_mod_order_spec`
  gives `k.asNat = sb.asNat 8 mod l`, so the scalar premises of the previous theorem hold. The
  translation does not include `sc_from_bytes`, because the reference module `scalar` is
  opaque. So the theorem states the reference scalar directly.

The scalar. The fork's `mul` reads a `Scalar` as the integer of its 32 bytes, `k.asNat`,
without a reduction mod `l`. Its spec needs `k.asNat < 2 ^ 255`, which dalek's `Scalar`
invariant gives. The reference reads a scalar as an element of `ZMod l`. So the reference
multiplies by `k.asNat mod l`. The two products are the same point if `k.asNat < l` or
`l • P = 0`. Evenness alone does not give the same point. For example, `P = (0, -1)` has order
2 and is even, and `k = l` gives `l • P = P` in dalek and the identity in the reference. For an
even point, the two products differ by a point of order dividing 4, so they have the same
Ristretto encoding. A scalar from `Scalar::from_bytes_mod_order` is below `l`, so for it
`mul_refines` gives the reference representative with no torsion condition on `P`. The
premises `OnCurve` and `LimbsLt n` on `P` remain.

Compared with track D, these theorems are about curve25519-dalek 5.0.0, as the fork translates
it, and not about the copy of 4.2.0. They also cover the i686 builds and the builds with
`precomputed-tables`. The decoding theorem relates the points, not the four coordinates:
the fork's `decompress` spec states only the represented point, so the dalek coordinates are
not compared. The encoding theorem has the fork's premises `LimbsLt n` and `OnCurve`, where
track D needs only limbs below `2 ^ 53`. Track D's real side of scalar multiplication was
open. Here it comes from the fork's `mul` spec.

### 7.2 Translation

`extract-ristretto-ref.sh` extracts `tracks/ristretto/ref-plain` with the Charon and Aeneas
release that the fork pins, with the entry points of track D and `-max-heartbeats 200000`.
The output `lean/RistrettoRef/Funs.lean` and `lean/RistrettoRef/Types.lean` differs from the
track D output (`tracks/ristretto/ref-plain/Ref/`) only by one added `set_option` line.
`ref-ristretto/` keeps the two Aeneas templates. `lean/RistrettoRef/FunsExternal.lean` and
`lean/RistrettoRef/TypesExternal.lean` are the track D field and scalar models, with the same
added line. The docstring of `fe_pow_p58` also gives the path of the track D lemma that it
cites. `--check` compares only the generated files and the templates. It does not check the
two hand-written models, which section 7.3 lists as assumptions.

`RistrettoRef` and `X25519Ref` both declare the root namespace `field`. So no module imports
both libraries, and the axiom checks of this section are in `lean/Checks/Ristretto.lean`.

### 7.3 Assumptions

The trusted base is that of section 4, with these changes:

1. For the reference theorems: the fork's `Ristretto.decodeRep`, `Ristretto.encodeRep`,
   `sqrtRatioM1`, `ZMod.IsNeg`, `ZMod.abs`, the constants `d`, `sqrtM1`, `invsqrtAMinusD`
   and `L`, and the group `curve25519.edwards` of EllipticCurve. The fork lists them in
   `Specs/Ristretto.lean` and `Defs/Ristretto.lean`.
2. The definitions in the statements of the dalek theorems. They are not axioms, but a reader
   must read them to know what a theorem says. A weaker `Rep` or a different `extRef` changes
   the result and does not change the `#print axioms` output. From this package
   (`Field.lean`, `Encoding.lean`, `Dalek.lean`):
   - `toF`: the ring isomorphism from `field.Fe` to `ZMod curve25519.p`.
   - `RefPt`: the reference extended coordinates `(X, Y, Z, T)`.
   - `refOf P`: the coordinates `(x, y, 1, x y)` of the affine point `P = (x, y)`.
   - `extRef E`: the four coordinates of a dalek point, read as reference field elements.
   - `Rep Q P`: `Z ≠ 0`, `X Y = Z T`, and `P = (X / Z, Y / Z)`.
   - `DecRel q r`: `q = Ok (refOf P)` if `r = some P`, and `q = Err 20` if `r = none`.

   From the fork: `toPoint`, `toExtended`, `OnCurve`, `LimbsLt`, `Even`, `Scalar.asNat`, `L`,
   `Scalar::from_bytes_mod_order`, and `•` on `curve25519.edwards.Point`.
3. The fork's axioms `RustAx.core` and `RustAx.subtle`. `zeroize` is not on these paths. The
   `decompress` and `compress` specs of the two i686 builds do not use `RustAx.core`.
4. The fork's translation, as in section 4.
5. The track D field and scalar models (`lean/RistrettoRef/FunsExternal.lean`,
   `lean/RistrettoRef/TypesExternal.lean`, track D README section 4).
6. The `ref-plain` port of the hacspec specs (track D README section 2).

`lean/Checks/Ristretto.lean` checks the axioms with `#guard_msgs`. `decode_spec`,
`encode_spec`, `ref_sqrt_ratio_m1`, `addExt_rep`, `point_mul_spec`, `point_mul_spec_of` and
`point_mul_encode_spec` use `propext`, `Classical.choice` and `Quot.sound` only. So do the
general compositions `*_of` of `Dalek.lean`, except
`from_bytes_decompress_mul_compress_refines_of`, which adds `RustAx.subtle` through the fork's
spec of `from_bytes_mod_order`. Each dalek theorem adds `RustAx.core` and `RustAx.subtle`,
except `decompress_refines` and `compress_refines` of the two i686 builds, which add
`RustAx.subtle` only.

### 7.4 Proof structure

| File | Lines | Content |
|---|---|---|
| `ForkCommon/Bytes.lean` | 29 | The two byte lemmas that `ForkSim` and `ForkRistretto` share |
| `ForkRistretto/Field.lean` | 235 | `toF`, the sign, `abs`, the bytes, the constants, and `geq_p` |
| `ForkRistretto/SqrtRatio.lean` | 148 | The reference `sqrt_ratio_m1` is the fork's `sqrtRatioM1` |
| `ForkRistretto/Encoding.lean` | 133 | `decode_spec` and `encode_spec` |
| `ForkRistretto/ScalarMul.lean` | 251 | `addExt_rep`, `point_mul_spec`, its corollaries, and the encoding of the product |
| `ForkRistretto/Dalek.lean` | 621 | The compositions, once for any build, then the theorems of the four builds |

1. `sqrt_ratio_m1`. The reference computes the candidate root `r = (u v³) (u v⁷)^((p-5)/8)`
   and tests `v r²`. The fork defines `sqrtRatioM1` by its properties. With `w = u v⁷`,
   `v r² = u t` for `t = w^((p-1)/4)`, and `t⁴ = 1` by Fermat's little theorem. So `t` is
   `±1` or `±√-1`, and in each case the reference result meets the fork's uniqueness lemmas.
   This is a new proof. Track D compared the reference with dalek's `sqrt_ratio_i` call by
   call instead.
2. `decode` follows `decodeRep` step by step. The accepted case builds the point with the
   fork's `decodeRep_equation` and `decodeRep_eq_some_iff`.
3. `encode` on `(X, Y, Z, T)` is the fork's `compressProj`, which the fork proves equal to
   `encodeRep` of the represented point (`compressProj_eq_encodeRep`).
4. Scalar multiplication. `addExt_rep` compares the reference `point_add` with the fork's
   affine formulas `addX` and `addY`, and takes the nonzero denominators from the
   completeness of the model. So the reference results land in the fork's group directly,
   and no isomorphism with track D's group `DalekSim.Edwards.Point dEd` is needed. For the
   encoding, `encodeRep_mod_nsmul` uses the fork's `even_iff_four_mul_L_nsmul` and
   `encodeRep_rel`: for an even `P`, `k • P - (k mod l) • P` is killed by 4, and the encoding
   does not see 4-torsion.
5. Composition. The section `Compose` of `Dalek.lean` proves each dalek theorem once, from
   the shapes of the fork's specs given as hypotheses. Each build states its theorems in full
   and applies these lemmas to its own specs. So the four copies differ only in their
   statements.

Copies of track D. Track D builds with Lean `v4.31.0` and this package with `v4.35.0`, so
this package cannot import track D. Three proofs are copied, with changes. `geq_p_loop_spec`
and its lemmas (`Field.lean`) come from `tracks/ristretto/lean/Sim/GeqP.lean`, with the
fork's `Array.asNat` in place of the digit sums of `DalekSim`. `point_mul_loop_spec`,
`point_mul_spec`, `point_mul_spec_nat` and `mod_two_pow_succ'` (`ScalarMul.lean`) come from
`tracks/ristretto/lean/Sim/ScalarMul.lean`, with the fork's group in place of
`DalekSim.Edwards.Point dEd`, and `ite_eq_left` and `ite_eq_right` in place of the
deprecated `if_pos` and `if_neg`. `addExt_rep` keeps the shape of the track D proof, with the
fork's formulas. `fe_from_bytes_eq` and `fe_to_bytes_val` (`Field.lean`) repeat the lemmas
of the same names in `ForkSim/X25519.lean`, because the two reference libraries cannot be
imported together. `fe_to_bytes_val` states the result as an existential here. The two byte
lemmas that do not use `field`, `foldr_range_eq_ofDigits` and `map_val_getElem!`, are in
`lean/ForkCommon/Bytes.lean`, which both libraries import. The other proofs are new.

No proof sets `maxHeartbeats` or uses `native_decide`.

### 7.5 Reproduce

As in section 6, then:

```bash
tracks/fork/extract-ristretto-ref.sh --check
```

```bash
cd tracks/fork/lean && lake build
```

After the X25519 build of section 6, the fork's `Specs.Ristretto` took 38 s of wall time
(7 min 11 s of CPU time) on the machine of this study. The files of this section then build
in 17 s.
