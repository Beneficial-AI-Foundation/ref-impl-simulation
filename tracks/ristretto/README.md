# Track D: Ristretto decoding and encoding (RFC 9496)

Track D proves that dalek's Ristretto decoding and encoding refine a reference. For every
32-byte input, `CompressedRistretto::decompress` returns without panic, overflow or divergence. The
reference `decode` returns a result, and the results agree. Both reject the same inputs.
On the other inputs, the two points have the same four coordinates. The theorem is
`RistrettoSim.decompress_refines` (section 3). It has no premises and uses only the three
standard axioms. For encoding, `RistrettoPoint::compress` returns without panic for every
point with limbs below `2^53`, and it returns the bytes of the reference `encode`. The
theorem is `RistrettoSim.compress_refines`. Its only premise is the limb bound, and it uses
only the three standard axioms.

All paths are relative to `tracks/ristretto/`.

## 1. Scope and sources

| Role | Code | Commit |
|---|---|---|
| Reference | [`hacspec/specs` `ristretto/src/ristretto.rs`](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/ristretto/src/ristretto.rs), old hacspec | `c511110d` |
| Reference library | [`hacspec/hacspec` `lib/`](https://github.com/hacspec/hacspec/tree/4ecc847fc944fe996e19423aa41f002f2039dab0/lib) | `4ecc847f` |
| Real | curve25519-dalek 4.2.0 as modified by `curve25519-dalek-lean-verify`, the copy of track B (`../x25519/real-dalek/curve25519-dalek`) | `26d49052` |

The track uses the clones of track B (`../x25519/hacspec-specs`, `../x25519/hacspec-old`).

The hacspec file says that it is modelled on dalek and was tested against dalek 3 with
QuickCheck. It follows the IETF draft `draft-irtf-cfrg-ristretto255-00`, not the final
RFC 9496. So the reference is not independent of the real code. The Rust tests and the Lean
vector checks compare it with the RFC 9496 test vectors (section 6).

libsignal `fc90b90f` uses curve25519-dalek 5.0.0 for Ristretto in `zkgroup`,
`zkcredential`, `poksho`, `usernames` and `svrb`. `compare-dalek5.py` compares
the 29 functions and constants on the path of the two theorems in 5.0.0 with the copy
proved here. After comments and blank lines are removed, 23 items are identical. Six items
differ in four ways, and the script fails on any other difference:

1. `add_assign` and `pow2k`: the two loop edits of track B.
2. `pow_p58` is `pub(crate)` in 5.0.0. The body is the same.
3. `sqrt_ratio_i`: 5.0.0 calls `r.conditional_negate(r_is_negative)`. The copy writes
   `let r_neg = -&r; r.conditional_assign(&r_neg, r_is_negative)`. This is the default
   method of `subtle::ConditionallyNegatable` (`subtle` 2.6.1).
4. `step_2` and `compress`: the copy binds subexpressions to names, and writes
   `conditional_negate` as in item 3. The field operations and their order are the same.

Decoding and encoding use only the serial field code. On 64-bit targets, the `simd` backend of dalek
does not change the field arithmetic. So the theorems cover decoding and encoding in every
libsignal build with 64-bit limbs. It does not cover a build with the `fiat` backend or with
`curve25519_dalek_bits = "32"`.

The theorems do not cover the group operations,
scalar multiplication, `from_uniform_bytes`, constant time or the erasure of secrets.

## 2. Translation

Both programs go through Charon and Aeneas into one Lake project (`lean/`), with the tool
versions of track B.

Reference. Aeneas fails on the original spec, because of `hacspec_lib` (Aeneas issue
#1164). `ref-plain/src/lib.rs` ports `decode`, `encode` and their helpers to plain Rust. The
field operations become calls into a module `field` (`ref-plain/src/field.rs`). In Rust,
this module wraps hacspec's `nat_mod` type, with the same definition as the spec, so the
port runs. Charon treats it as opaque. The port keeps the order of the field operations of
the spec. It also makes these changes:

1. The constants `D`, `SQRT_M1` and `INVSQRT_A_MINUS_D` are little-endian byte arrays,
   decoded by `fe_from_bytes`. The spec decodes big-endian bytes.
2. The `for` loop of `geq_p` is a `while` loop.
3. `is_negative`, `eq` and the exponent of `sqrt_ratio_m1` are calls into `field`
   (`fe_is_negative`, `fe_eq`, `fe_pow_p58`), with the expressions of the spec.

In Lean, the field module is written by hand over `ZMod (2^255 - 19)`
(`lean/RistrettoRef/FunsExternal.lean`, section 4).

Real. Charon starts from `CompressedRistretto::decompress` and `RistrettoPoint::compress` in
the dalek copy of track B, with the serial u64 backend. The Aeneas output needs no hand
edits. `lean/Curve25519Dalek/Funs.lean` and `Types.lean` are copies of `real/Rist/`, and
`check.sh` makes sure that they stay the same. The output has 7 external functions and the
external type `subtle.Choice`. `lean/Curve25519Dalek/FunsExternal.lean` defines all of them
(section 4).

Field proofs. The track copies the field specs that track B ported to Aeneas `d119a474`
(`lean/Curve25519Dalek/Specs/`), without changes. It also copies `negate_spec` from
`curve25519-dalek-lean-verify` `26d49052`. That proof checks on `d119a474` without changes.
The other specs of the path are new proofs in `lean/Sim/` (section 5). They do not use the
`sqrt_ratio_i`, `step_1`, `step_2` or `decompress` specs of `curve25519-dalek-lean-verify`.
Those specs depend on axioms for `subtle` and on `bv_decide` native code.

## 3. Statement

The main theorem is `RistrettoSim.decompress_refines` (`lean/Sim/Decode.lean`):

```lean
theorem decompress_refines (b : Array U8 32#usize) :
    ristretto.CompressedRistretto.decompress b ⦃ r =>
      ∃ q, ristretto_ref.decode b = ok q ∧ DecRel q r ⦄
```

`⦃ ⦄` is the Aeneas total-correctness triple. The theorem has no premises. The relation of
the results is:

```lean
def toZPt (P : edwards.EdwardsPoint) : RefPt := (toZ P.X, toZ P.Y, toZ P.Z, toZ P.T)

def DecRel : core.result.Result RefPt U8 → Option ristretto.RistrettoPoint → Prop
  | .Ok q, some P => q = toZPt P ∧ BndPt 52 P
  | .Err e, none => e = 20#u8
  | _, _ => False
```

`toZ` is the relation of track B. It reads the five limbs of a `FieldElement51` in radix
`2^51` and reduces mod `p = 2^255 - 19`. `BndPt 52 P` states that every limb of the four
coordinates is below `2^52`. `20` is the `DECODING_ERROR` of the spec.

So, for every input, either both programs reject it, or both accept it and return the same
four coordinates. The coordinates are equal as elements of the field, not only as points of
the Ristretto group. This is possible because the two programs compute the same
representative `(x, y, 1, x y)`.

The second theorem is `RistrettoSim.sqrt_ratio_i_refines` (`lean/Sim/SqrtRatio.lean`). If
the limbs of `u` and `v` are below `2^54`, dalek's `sqrt_ratio_i u v` returns the result of
the reference `sqrt_ratio_m1 (toZ u) (toZ v)` under `toZ`.

The encoding theorem is `RistrettoSim.compress_refines` (`lean/Sim/Encode.lean`):

```lean
theorem compress_refines (P : ristretto.RistrettoPoint) (hP : BndPt 53 P) :
    ristretto.RistrettoPoint.compress P ⦃ c =>
      ristretto_ref.encode (toZPt P) = ok c ⦄
```

The premise states that every limb of the four coordinates is below `2^53`. This is the
bound of `EdwardsPoint.IsValid` in `curve25519-dalek-lean-verify`. The proof needs it
because the spec of `add` (for `Z + Y`) requires limbs below `2^53`. The theorem does not
need the curve equation, because both programs do the same field operations. So it holds
also for tuples that are not points. The two results are equal bytes.

`RistrettoSim.decompress_compress_refines` composes the two theorems. For every input, it
states the result of `decompress_refines`. In addition, if `decompress` returns a point,
`compress` of that point returns the bytes of `encode` on the point of `decode`. A decoded
point has limbs below `2^52`, so the premise of `compress_refines` holds.

The theorems do not prove that `encode (decode b) = b` for an accepted `b`. That is a
fact about the reference alone, and only the tests of section 6 check it.

## 4. Assumptions

Premises. `decompress_refines` has none. `compress_refines` has the limb bound of
section 3.

Trusted definitions. `#print axioms` does not show them.

1. The port to plain Rust computes the same as the hacspec spec. Its Rust tests compare the
   port with the unchanged spec and with dalek 5.0.0 (section 6).
2. The Lean field model computes the same as hacspec's `nat_mod`. `field.Fe` is
   `ZMod (2^255 - 19)` (`lean/RistrettoRef/TypesExternal.lean`). `fe_add`, `fe_sub`,
   `fe_mul` and `fe_sq` are the ring operations. `fe_eq` is equality. `fe_is_negative` tests
   that the canonical representative is odd. `fe_pow_p58` raises to the power
   `(p - 5) / 8`. `fe_from_bytes` decodes all 256 bits little-endian and reduces mod `p`.
   `fe_to_bytes` encodes the canonical representative. `fe_lit` is the cast of a number.
3. The 7 hand definitions for `subtle` on the real side
   (`lean/Curve25519Dalek/FunsExternal.lean`) and the type `subtle.Choice`
   (`lean/Curve25519Dalek/TypesExternal.lean`). A `Choice` carries a proof that its value is
   0 or 1. The definitions follow `subtle` 2.6.1 on these values:
   `Choice::from(u8)` (copied from track B), `bool::from(Choice)`, `not`, `bitor`, `ct_eq` on
   `u8` and on slices, and `conditional_assign` on `u64`. Rust computes them with bit
   operations in constant time. If the lengths differ, the slice `ct_eq` returns 0.
   Otherwise it starts from the value 1 and folds `&=` over the elementwise `ct_eq`, as
   Rust does.
4. The real code is the modified copy of dalek in `curve25519-dalek-lean-verify`. The
   theorem holds for that copy.

Axioms. `lean/Sim/Axioms.lean` checks with `#guard_msgs` that `decompress_refines`,
`compress_refines`, `decompress_compress_refines` and `sqrt_ratio_i_refines` depend only on `propext`, `Classical.choice` and `Quot.sound`.

## 5. Proof structure

| File | Lines | Content |
|---|---|---|
| `Sim/Field.lean` | 150 | The relation `toZ`, the field specs over `toZ`, `pow_p58` and `negate` |
| `Sim/Bytes.lean` | 120 | Base-256 digits, copied from track B |
| `Sim/Choice.lean` | 203 | Slice `ct_eq` on 32 bytes, field `ct_eq`, `is_negative`, `is_zero`, `conditional_assign` |
| `Sim/Consts.lean` | 75 | `EDWARDS_D`, `SQRT_M1`, `INVSQRT_A_MINUS_D` and `ONE` against the reference constants |
| `Sim/SqrtRatio.lean` | 159 | The reference `sqrt_ratio_m1` in closed form, and `sqrt_ratio_i_refines` |
| `Sim/GeqP.lean` | 124 | The reference `geq_p` loop computes `p ≤ x` |
| `Sim/Decode.lean` | 368 | `step_1`, `invsqrt`, `step_2`, the reference `decode` in three cases, and `decompress_refines` |
| `Sim/Encode.lean` | 245 | The reference `encode` in closed form, `compress_refines` and `decompress_compress_refines` |

The proof goes call by call. For each real field operation, a spec gives the value under
`toZ` and a limb bound. The reference side is a pure computation in `ZMod p`, and a closed
form of it is proved by unfolding. The values then agree by ring identities, for example
`-(d u1²) - u2² = (-d) u1² - u2²`.

The rejection tests need two more arguments. First, dalek reads the low 255 bits and
compares `to_bytes` of the result with the input. The reference rejects inputs `≥ p` with
the loop `geq_p`. `step_1_z` and `geq_p_spec` show that both tests reject exactly the inputs
`≥ p`. Second, the `subtle` tests return a `Choice`, and the reference returns a `bool`.
For each `Choice` lemma, the statement gives the condition for the value 1.

No proof in `lean/Sim/` sets `maxHeartbeats` or `maxRecDepth`. Some of the field specs
copied from track B set `maxRecDepth 4096`, as in track B.

## 6. Checks

1. `cargo test` in `ref-plain/` passes `tests/rfc.rs`. Each case decodes and encodes with
   the port, with the unchanged hacspec spec and with dalek 5.0.0, and compares the three
   results. The cases are the 16 encodings of RFC 9496 A.1 and the 29 invalid encodings of
   A.2. There are also 44 edge inputs and 2000 random inputs from a fixed seed. The edge
   inputs are values near 0 and `p`, and values with the top bit set.
2. `lake build` in `lean/` passes. No file in `lean/` has a `sorry`.
3. `Sim/Axioms.lean` checks the axiom lists of section 4 with `#guard_msgs`.
4. `Sim/RefVectors.lean` runs the Lean reference, with the `ZMod` model, on the vectors of
   RFC 9496 A.1 and A.2, with `#guard`. This trusts the Lean compiler, and it is a test,
   not a proof.
5. `check.sh` makes sure that the Lean copies of the Aeneas output are the same as
   `ref-plain/Ref/` and `real/Rist/`.
6. `scripts/check-short-names.py` finds no name in `lean/RistrettoRef` and
   `lean/Curve25519Dalek` that Lean binds to a different declaration (Aeneas issue #1458).
7. `compare-dalek5.py` checks the proved path against dalek 5.0.0 (section 1). With
   `--self-test`, it changes each item of the 5.0.0 tree in memory and checks that the
   comparison reports the change.

`check.sh` runs these checks and stops at the first failure.

## 7. Strengths and weaknesses

Strengths:

1. The decoding theorem covers every 32-byte input. It has no premises. The encoding
   theorem covers every tuple with the limb bound of a valid point. The axioms are only the
   standard three.
2. The relation is equality of the four coordinates in the field, which is stronger than
   equality in the Ristretto group.
3. The proof does not depend on the group law of Edwards curves. dalek-lean's statement of
   that law depends on a `sorry` (`add_assoc_Ed25519`).
4. The real side has no axioms. All `subtle` functions on the path have definitions.
5. The proved path is the decoding and encoding code of libsignal's builds with 64-bit limbs, apart from
   the reviewed edits of section 1.

Weaknesses:

1. The reference follows dalek. A shared error in the two programs is not found.
2. The reference is a port, and the field model is hand-written. Their faithfulness rests
   on review and on the tests of section 6.
3. The `subtle` definitions state the result of constant-time code. The theorem says
   nothing about constant time.
4. The theorems cover decoding and encoding only. Scalar multiplication is a later stage.
5. No theorem states that `encode (decode b) = b`. Only tests check it.

## 8. Reproduce

From the repository root, run `scripts/fetch-upstreams.sh` once. The tests need
curve25519-dalek 5.0.0 in the cargo registry. Then run every check:

```bash
tracks/ristretto/check.sh
```

To skip the comparison with 5.0.0, set `SKIP_DALEK5=1`.

The extraction commands. Run the first two in `ref-plain/`, with the Aeneas release of
`.aeneas/` on `PATH`:

```bash
charon cargo --preset=aeneas --start-from crate::decode --start-from crate::encode --opaque crate::field -- --offline
aeneas -backend lean -split-files -loops-to-rec -namespace ristretto_ref -dest Ref ristretto_ref.llbc
```

Run the next two in `../x25519/real-dalek/`. Then copy `Rist/` to `real/Rist/`:

```bash
charon cargo --preset=aeneas --start-from 'crate::ristretto::CompressedRistretto::decompress' --start-from 'crate::ristretto::RistrettoPoint::compress' -- --locked --offline -p curve25519-dalek --no-default-features --features alloc,zeroize
aeneas -backend lean -loops-to-rec -split-files -dest Rist curve25519_dalek.llbc
```

`lean/RistrettoRef` and `lean/Curve25519Dalek` hold copies of `ref-plain/Ref` and
`real/Rist` without hand edits, plus the hand-written external files of section 4.
