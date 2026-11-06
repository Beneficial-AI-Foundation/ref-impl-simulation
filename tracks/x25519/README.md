# Track B: X25519 (RFC 7748)

Track B proves full refinement for five functions of x25519-dalek against the reference.
For every 32-byte scalar and u-coordinate, x25519-dalek's `x25519` returns without panic,
overflow or divergence, and the reference `x25519_scalarmult` returns the same 32 bytes. The
theorem is `X25519Sim.x25519_refines` (section 3). The same holds for `diffie_hellman` on
`StaticSecret`, the type that libsignal uses, on `EphemeralSecret` and on `ReusableSecret`.
`x25519` on the constant `X25519_BASEPOINT_BYTES` agrees with `x25519_secret_to_public`.
`SharedSecret::was_contributory` after `diffie_hellman` returns `true` iff the reference
result is not all zero. The all-zero check is our addition to the reference (section 1). The
six accessors `to_bytes` and `as_bytes` are proved to be the identity. The theorems have no
premises and use only the three standard axioms. `x25519` and the three `diffie_hellman`
methods call curve25519-dalek's `MontgomeryPoint::mul_clamped`, and
`X25519Sim.mul_clamped_refines` proves the same result for that function. Key generation,
public-key derivation, the `From` and `AsRef` conversions and the trait impls are not
covered. Section 1 lists them, with the gaps between RFC 7748, the reference and
x25519-dalek.

All paths are relative to `tracks/x25519/`, except the paths that start with `shared/` or
`scripts/`. Those are relative to the repository root.

## 1. Scope and sources

| Role | Code | Commit |
|---|---|---|
| Reference | [`hacspec/specs` `curve25519/src/curve25519.rs`](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/curve25519/src/curve25519.rs), old hacspec | `c511110d` (2025-04-22) |
| Reference library | [`hacspec/hacspec` `lib/`](https://github.com/hacspec/hacspec/tree/4ecc847fc944fe996e19423aa41f002f2039dab0/lib) | `4ecc847f` |
| Real | [curve25519-dalek 4.2.0 as modified by `curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek) | `26d49052` |
| Real wrapper | [x25519-dalek 2.0.1](https://github.com/dalek-cryptography/curve25519-dalek/tree/4ac84dd0668b1d2e51654fcdffe4ae6a687bef00/x25519-dalek), from crates.io, unchanged | `4ac84dd0` |

The track relates the X25519 function of the two programs: the real
`x25519_dalek::x25519` against the reference `x25519_scalarmult`. The proof goes through the
layers of the call path: `mul_clamped`, clamping, decoding, the ladder, the ladder step and
encoding. The ladder step, the
reference `point_add_and_double` against the real `montgomery::differential_add_and_double`,
was the first layer proved. The subsection "Layers of the full refinement" shows all
layers.

libsignal computes X25519 agreement through `x25519-dalek` 3.0.0 and curve25519-dalek
5.0.0 (libsignal `fc90b90f`). `PrivateKey::calculate_agreement(&self, u)` computes
`self.secret.diffie_hellman(&PublicKey::from(u)).as_bytes()`. `self.secret` is a
`StaticSecret` that `PrivateKey` built earlier with `StaticSecret::from`. `diffie_hellman`
calls `MontgomeryPoint::mul_clamped`. libsignal does not call `x25519_dalek::x25519`.
x25519-dalek 3.0.0 needs curve25519-dalek 5, so the track extracts x25519-dalek 2.0.1, which
builds on the 4.2.0 copy. `compare-dalek5.py` compares 88 functions, constants, macros and
structs: 66 items of curve25519-dalek 5.0.0 against the copy proved here, and 22 items of
x25519-dalek 3.0.0 against 2.0.1. It finds each item by its `impl` block and its name, and
fails if an item is missing or ambiguous. The crate checksums of 5.0.0 and 3.0.0 match
libsignal's `Cargo.lock`. After comments and blank lines are removed, 74 items are
identical, 13 differ and 1 is absent in 5.0.0. The script fails on any difference that it
does not list as reviewed.

34 items of curve25519-dalek and 14 of x25519-dalek are on the paths of the full theorems.
The 14 items are `x25519`, `X25519_BASEPOINT_BYTES`, the three `diffie_hellman` methods,
the six accessors `to_bytes` and `as_bytes` of `StaticSecret`, `PublicKey` and
`SharedSecret`, `was_contributory`, and the two `From<[u8; 32]>` impls of `StaticSecret`
and `PublicKey`. Of these, 44 are identical, the 14 items of x25519-dalek among them. Four
items differ through three extraction edits:

1. `add_assign` uses `while` in place of `for i in 0..5`.
2. `pow2k` uses `while k > 0` in place of `loop` with `break` at `k == 0`. Its callers
   pass `k ≥ 1`. Its five `debug_assert!`s are removed.
3. The ladder `mul` calls `mul_bits_be(scalar.bits_le().rev().skip(1))` in 5.0.0. The copy
   inlines this loop as an index loop over bits 254 down to 0, with the same bit read, and
   writes `prev_bit != cur_bit` in place of `prev_bit ^ cur_bit`. The script compares the
   copy's `mul` with 5.0.0's `mul`, and `mul_bits_be` with `mul_bits_be`, which differs by
   the same `!=`. The copy's `mul_bits_be` is not on its proved path.

The identical items include `from_bytes`, `to_bytes`, `reduce`, `from_limbs`, `invert`,
`pow22501`, `differential_add_and_double`, `as_affine`, both `conditional_select`s,
`mul_clamped`, `MontgomeryPoint::to_bytes`, `MontgomeryPoint::as_bytes`, `clamp_integer`,
`bits_le`, the multiplication wrappers, the `ct_eq` of `FieldElement` and of
`MontgomeryPoint`, `MontgomeryPoint::identity`, the blanket `is_identity` and the 14 items
of x25519-dalek.

The other 32 items of curve25519-dalek and 8 of x25519-dalek are on the paths of work that
is not proved yet: the public key `PublicKey::from(&secret)`, which goes through
`MontgomeryPoint::mul_base_clamped`, `EdwardsPoint::mul_base`, the basepoint table and
`to_montgomery`, and the drop code of the secret types in 3.0.0. The result is in
the next list. "Matters" says whether the difference changes what a proof about the copy
shows for 5.0.0.

Identical, 27 items of curve25519-dalek: `MontgomeryPoint::mul_base` and
`mul_base_clamped`. Of
`EdwardsPoint`: `mul_base`, `mul_base_clamped`, `to_montgomery`, `double`,
`as_affine_niels`, `ct_eq`, `identity` and the struct. The macro `impl_basepoint_table` and
its call for `EdwardsBasepointTable` (`Radix = 4`, `Additions = 64`). The call of
`impl_lookup_table` for `LookupTable`. For `AffineNielsPoint`: `identity`,
`conditional_select`, `conditional_assign`, `Neg for &AffineNielsPoint`, `&EdwardsPoint +
&AffineNielsPoint` and the struct. `ProjectivePoint::as_extended` and `double`,
`CompletedPoint::as_projective` and `as_extended`. The constants `EDWARDS_D2` and
`ED25519_BASEPOINT_POINT`, and the basepoint table: `ED25519_BASEPOINT_TABLE` and its data
`ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`, 5,954 lines of limbs. So a check of the table
limbs of the copy also holds for 5.0.0. The copy's `mul_base` of the table still has the
iterator `filter`, and so has 5.0.0, so an edit that removes it applies to both.

Identical, 3 items of x25519-dalek: the three `PublicKey::from(&secret)`.

Changed, 4 items of curve25519-dalek, 5 of x25519-dalek, and 1 absent:

1. `EdwardsPoint::mul_by_pow_2`: the copy has a `while` loop with a counter, and 5.0.0 has
   `for _ in 0..(k - 1)`. This is an extraction edit of the copy, like `add_assign`. Matters:
   no. The loop is the same. A port needs the same edit.
2. `Scalar::as_radix_16`: the copy has two `while` loops with counters in place of
   `for i in 0..32` and `for i in 0..63`. Matters: no. A port needs the same edit.
3. `Scalar::as_radix_2w`: the copy writes `(256 + w - 1) / w` where 5.0.0 has
   `256_usize.div_ceil(w)`, and `if w == 8` where 5.0.0 has `match w`. Both agree for every
   `w > 0`, and the table passes `w = 4`. Matters: no. A port needs the same two edits.
4. `impl_lookup_table`, which holds `select` of the table: 5.0.0 calls
   `t.conditional_negate(neg_mask)` and requires `ConditionallyNegatable`. The copy
   writes `let t_neg = -t; t.conditional_assign(&t_neg, neg_mask)`. This is the default
   method of `subtle::ConditionallyNegatable` (`subtle` 2.6.1), with `-&t`. Matters: yes,
   for the port. A proof about the copy's `select` does not cover the call of
   `conditional_negate`. The proof for 5.0.0 needs a model of that method, as in track D, or
   the edit of the copy. 5.0.0 has no owned `Neg for AffineNielsPoint` any more, and the
   script lists it as absent. It only calls `-&self`, so nothing is lost.
5. The structs `PublicKey`, `EphemeralSecret`, `ReusableSecret`, `StaticSecret` and
   `SharedSecret`: 2.0.1 has `derive(Zeroize)` and `zeroize(drop)` under the feature
   `zeroize`. 3.0.0 has explicit `impl Drop` blocks that call `self.0.zeroize()`, plus
   `impl ZeroizeOnDrop`, and for `PublicKey` an explicit `impl Zeroize`. Matters: not for
   the returned bytes. For `EphemeralSecret::diffie_hellman`, which takes `self` by value,
   the drop of the secret is on the path in both versions. The 3.0.0 `Drop` impls exist
   even without the feature `zeroize`, with an empty body. In the extraction of 2.0.1,
   Charon reaches the `Drop` impl of `EphemeralSecret`, and Aeneas emits no call to it
   (section 2). The track does not extract 3.0.0, so the translation of its drop code is
   not known. A theorem about return values does not see the erasure.
   `ephemeral_diffie_hellman_refines` covers the returned bytes on 2.0.1.

Not compared, because they are not on the path: `random_from_rng`, `random` and the removed
`new` (3.0.0 uses `getrandom` and takes `&mut R`), `to_montgomery_batch`, and the
multiscalar and variable-time code. The script does not read `subtle`. libsignal
`fc90b90f` locks `subtle` 2.6.1 in its `Cargo.lock`, the version that the proofs of the copy
assume. `check.sh` checks this if you set `LIBSIGNAL_LOCK` to that lock file.

Size of a port of the extraction edits to 5.0.0, as an estimate from this comparison: the
8 changed items of curve25519-dalek differ from the copy in 67 lines (41 on the ladder path
and 26 in the table path), and no difference changes a value. The table, its macros and the
other 57 items accept the edits of the copy as they are. The only new proof work is the
model of `conditional_negate`. The estimate does not cover edits of the copy outside the
listed items, which the script does not see. The port is not started.

The comparison covers libsignal builds with the serial u64 field backend: every 64-bit
target, and the 32-bit Android targets, because libsignal's `java/build_jni.sh` sets
`curve25519_dalek_bits = "64"` there. It does not cover a build with the `fiat` backend or
with `curve25519_dalek_bits = "32"`. libsignal builds dalek with
`overflow-checks = false` in release. The theorems show that no arithmetic on the paths
overflows, so this setting does not change the result.

### Layers of the full refinement

Full refinement here is a theorem about one API pair. It relates the real
`x25519_dalek::x25519` to the reference `x25519_scalarmult` on all 32-byte inputs. Both
functions take a scalar and a u-coordinate as bytes and return the result as bytes. The
table follows the call path from this pair down to the ladder step. The theorem
`X25519Sim.x25519_refines` (section 3) relates the first pair and every pair from "Clamped
multiplication" down. The theorems for the other rows share every layer below
`mul_clamped`.

| Layer | Reference (`lean/X25519Ref`) | Real (`lean/X25519Dalek`, `shared/dalek/lean/Curve25519Dalek`) | Status | Lean |
|---|---|---|---|---|
| X25519 function | `x25519_scalarmult` | `x25519_dalek::x25519` | proved | `Sim/X25519.lean` |
| Shared secret | `x25519_scalarmult` | `diffie_hellman` on `StaticSecret`, `EphemeralSecret` and `ReusableSecret`, and `SharedSecret::as_bytes` | proved | `Sim/X25519.lean` |
| Public key through the bare function | `x25519_secret_to_public` | `x25519` on `X25519_BASEPOINT_BYTES` | proved | `Sim/X25519.lean` |
| Accessors | none: the identity on the bytes | `to_bytes` and `as_bytes` of `StaticSecret`, `PublicKey` and `SharedSecret` | proved | `Sim/X25519.lean` |
| All-zero check | `x25519_scalarmult`, then `x25519_is_all_zero` (our addition) | `diffie_hellman`, then `SharedSecret::was_contributory` | proved | `Sim/Contributory.lean` |
| Clamped multiplication | `x25519_scalarmult` | `MontgomeryPoint::mul_clamped` | proved | `Sim/Full.lean` |
| Scalar clamping | `decode_scalar`, `mask_scalar` | `scalar::clamp_integer` | proved | `Sim/Full.lean` |
| Point decoding | `decode_point` | `FieldElement51::from_bytes` | proved | `Sim/Full.lean`, `Sim/Bytes.lean` |
| Ladder | `montgomery_ladder` | `Mul<&Scalar> for &MontgomeryPoint` | proved | `Sim/LadderMath.lean`, `Sim/RefSide.lean`, `Sim/RealSide.lean` |
| Ladder step | `point_add_and_double` | `differential_add_and_double` | proved | `Sim/Pilot.lean`, `Sim/Discharge.lean` |
| Point encoding | `encode_point` | `ProjectivePoint::as_affine` | proved | `Sim/Full.lean`, `Sim/Bytes.lean` |

The layers needed these results:

1. Clamping and decoding. `clamp_integer` and `mask_scalar` have the same code, so the
   Lean definitions are equal by `rfl`. `decode_point` clears bit 255 and reads the bytes.
   `from_bytes` reads the low 255 bits. Both give `U8x32_as_Nat u % 2 ^ 255` mod p.
2. The ladder. The reference runs 256 iterations from bit 255, with a swap before and
   after each step. dalek runs 255 iterations from bit 254, with lazy swaps and one swap at
   the end. `mul_loop_spec` shows that dalek's logical state, the physical pair swapped by
   the last bit, follows the reference iteration on each bit. The invariant also carries
   the limb bound `2 ^ 52`. The masked scalar has bit 255 equal to 0, so the reference runs
   one extra step. After that step, the second point is dalek's point times `4 u`. Each
   later step scales each point by a nonzero factor, and the encoding `x / z` cancels the
   factor (`enc_ladder_extra_step`). If `u = 0`, both encodings are 0.
3. Encoding. `invert` computes `z ^ (p - 2)`, which is `z⁻¹` in `ZMod p`, with `0⁻¹ = 0`.
   `to_bytes` returns the canonical representative, and the bytes of a number below `p`
   are its base-256 digits, so they equal `fe_to_bytes`.
4. Composition. `mul_clamped_refines` chains the layers below `mul_clamped`.
5. The wrapper. `x25519(k, u)` is `MontgomeryPoint(u).mul_clamped(k).to_bytes()`.
   `MontgomeryPoint` is a 32-byte array, and `to_bytes` returns it. `x25519_refines`
   composes `mul_clamped_refines` with this step.
6. The shared secret. `StaticSecret::diffie_hellman(&self, their_public)` is
   `SharedSecret(their_public.0.mul_clamped(self.0))`, and `SharedSecret::as_bytes`
   returns the bytes of the point. `static_diffie_hellman_refines` and
   `static_diffie_hellman_as_bytes_refines` compose `mul_clamped_refines` with these
   steps. `EphemeralSecret::diffie_hellman` and `ReusableSecret::diffie_hellman` have the
   same body. `EphemeralSecret::diffie_hellman` takes `self` by value, so Rust drops the
   secret at the end and erases its bytes. The extraction has no call to the `Drop` impl, so
   the Lean body is the same as for `StaticSecret`. The theorem covers the returned bytes
   on 2.0.1 (section 1, item 5).
7. The base point and the accessors. `X25519_BASEPOINT_BYTES` is 9 followed by 31 zero
   bytes, the base that `x25519_secret_to_public` builds (`basepoint_eq`). So
   `x25519_basepoint_refines` follows from `x25519_refines`. The six accessors return the
   32 bytes that they wrap, so each one is the identity in Lean.
8. The all-zero check. `was_contributory` is `!self.0.is_identity()`. The identity is 32
   zero bytes, and `MontgomeryPoint::ct_eq` decodes both sides with `from_bytes` and compares
   them in `ZMod p` (`was_contributory_spec`). Our reference function
   `x25519_is_all_zero` computes the OR of the 32 bytes, as RFC 7748, section 6.1,
   suggests, and compares it with 0 (`is_all_zero_eq`). The two checks agree on bytes that
   read as a number below `p`, and `x25519_scalarmult` returns such bytes
   (`x25519_scalarmult_canonical`). `was_contributory_refines` combines these facts.

The real side reuses specs of `curve25519-dalek-lean-verify` at commit `26d49052`:
`from_bytes`, `to_bytes`, `pow22501` and `invert`, ported to the Aeneas version of this
project (section 2). Its ladder spec, `mul_loop_spec`, has three `sorry`s at that commit,
so this track proves its own.

### Gaps: RFC 7748, the reference and x25519-dalek

Refinement is relative to the reference. A real function without a counterpart in the
reference is not covered, and the theorems say nothing about it. This section states the
gaps at three levels: what the RFC describes, what the hacspec reference has, and what
x25519-dalek 2.0.1 offers. It covers the Curve25519 part of the RFC.

| RFC 7748 | hacspec `curve25519` | x25519-dalek 2.0.1 | Status |
|---|---|---|---|
| Section 5: the function `X25519(k, u)`. Mask bit 255 of `u` (MUST), accept non-canonical `u` (MUST) | `x25519_scalarmult` | `x25519` | proved (`x25519_refines`). For the translated reference, `decode_point_spec` (`lean/Sim/Full.lean`) proves both MUST rules under the trusted field model: it reads `u` as `u mod 2^255` in `ZMod p`. That the unchanged hacspec spec and the field model match the RFC rests on review and tests |
| Section 6.1: the shared secret `X25519(a, K_B)` | `x25519_scalarmult` (no function of its own) | `diffie_hellman` on `EphemeralSecret`, `ReusableSecret`, `StaticSecret` | proved for the three types (`static_diffie_hellman_refines`, `ephemeral_diffie_hellman_refines`, `reusable_diffie_hellman_refines`, and `static_diffie_hellman_as_bytes_refines` with `SharedSecret::as_bytes`) |
| Section 6.1: the public key `X25519(a, 9)` | `x25519_secret_to_public` | `PublicKey::from(&secret)` for the three secret types | not proved for `PublicKey::from(&secret)`. The real code goes through `EdwardsPoint::mul_base_clamped`, with precomputed base point tables if the feature `precomputed-tables` is on. The shared library extracts this path with the feature and proves the table (`basepoint_table` in `shared/dalek/lean/DalekSim/BasepointTable.lean`). That theorem holds for the table after the edit `shared/dalek/inline-table.py`, which Lean does not check. The specs of the functions on the path are open. The bare `x25519(a, X25519_BASEPOINT_BYTES)` is proved against `x25519_secret_to_public` (next row) |
| Section 6.1: the base point 9 | inside `x25519_secret_to_public` | `X25519_BASEPOINT_BYTES` | proved: the constant is the base of the reference (`basepoint_eq`), and `x25519` on it agrees with `x25519_secret_to_public` (`x25519_basepoint_refines`) |
| Section 6.1: Alice generates 32 random bytes | missing | `random_from_rng`, `random` (feature `getrandom`) and the deprecated `new` on the three secret types | not covered. The reference does not describe it, and functional refinement cannot state that bytes are random |
| Sections 6.1 and 7: check for the all-zero shared secret (MAY), for example by an OR of all bytes | missing. We added `x25519_is_all_zero` to the port: the OR of all bytes, compared with 0 | `SharedSecret::was_contributory` | proved after `diffie_hellman` on the three secret types, against `x25519_scalarmult` and then the negation of `x25519_is_all_zero` (`static_diffie_hellman_was_contributory_refines` and the two others). dalek ignores bit 255 and compares with 0 mod p, so it also reports 0 for non-canonical encodings of 0. `SharedSecret` has no public constructor, and `diffie_hellman` returns canonical bytes, so this case does not occur through the API. For this reason, the theorems state the composition. That `x25519_is_all_zero` matches the RFC rests on review and tests |
| Sections 6.1 and 7: a key-derivation function of `K`, `K_A` and `K_B`, and public keys bound into it | missing | missing | outside the track. The caller derives the symmetric key |
| Sections 5.1 and 7: side channels | not expressible | constant-time code through `subtle` | outside functional refinement |
| Sections 5.2 and 6.1: test vectors | some, in its tests | its tests | the track runs the two vectors of section 5.2, the iterated test after 1 and 1,000 iterations, and all values of section 6.1 (section 6). The test after 1,000,000 iterations is an ignored Rust test, because it runs for hours on the bignum field of hacspec |
| Sections 4.2, 5 and 6.2: X448 | missing | missing | outside the track |

So the hacspec reference misses two parts of Curve25519 Diffie-Hellman in the RFC: key
generation and the all-zero check. The port adds the all-zero check. Key generation stays
out, because functional refinement cannot state that bytes are random. The reference also
has no X448. Key derivation is missing on both sides and is left to the caller.

x25519-dalek has these public APIs that the RFC does not describe:

1. Three secret types instead of 32 private bytes: `EphemeralSecret`, `ReusableSecret`
   (feature `reusable_secrets`) and `StaticSecret` (feature `static_secrets`).
   `EphemeralSecret::diffie_hellman` consumes the secret, and the type has no `Clone` and
   no accessor. `ReusableSecret` can be used many times and cloned, but it has no accessor
   and no `serde`. `StaticSecret` can also be read, built from bytes and serialized. These
   are usage rules, not computations.
2. Conversions and accessors: `From<[u8; 32]>` for `PublicKey` and `StaticSecret`, and
   `to_bytes`, `as_bytes` and `AsRef<[u8]>` on `PublicKey`, `StaticSecret` and
   `SharedSecret`. They wrap and unwrap 32 bytes. `StaticSecret::to_bytes` returns the
   private bytes. The theorems cover `to_bytes` and `as_bytes` of the three types. The two
   `From<[u8; 32]>` impls and the three `AsRef<[u8]>` impls are not extracted, because Charon
   cannot start from them (section 2).
   The `From` impls are linked to the theorems by review (section 4, source
   correspondence). Each `AsRef` impl returns the bytes as a slice.
3. Traits: `PartialEq`, `Eq`, `Hash`, `Copy`, `Clone` and `Debug` on `PublicKey`, and
   `Clone` on `ReusableSecret` and `StaticSecret`. With the feature `zeroize`, all five
   types implement `Zeroize`, and the three secret types and `SharedSecret` also erase
   their bytes on drop. `PublicKey` does not. With the feature `serde`, `PublicKey` and
   `StaticSecret` implement `Serialize` and `Deserialize`. `PublicKey` equality ignores
   bit 255 and compares mod p, so two keys with different bytes can be equal. `Hash` uses
   the canonical bytes, so it agrees with this equality. The RFC defines no equality of
   keys.

The theorems also say nothing about constant time or about the erasure of secrets.

## 2. Translation

Both programs go through Charon and Aeneas. The Lake project `lean/` holds the reference,
the x25519-dalek wrapper and the proofs. It requires the shared library of curve25519-dalek
([`shared/dalek`](../../shared/dalek/README.md)).

Reference. Aeneas fails on the original spec, because of the supertraits of
`hacspec_lib::SeqTrait` (Aeneas issue #1164). The track uses a port to plain Rust
(`ref-plain/src/lib.rs`, 229 changed lines against the 110-line spec, plus the new
32-line `ref-plain/src/field.rs`). Of the 229 lines, 166 are the port, and 63 are our
all-zero check and the new RFC tests. The unchanged spec, as a crate, is in `ref-hacspec/`.
The port also has our addition `x25519_is_all_zero`, a 9-line function that the spec does
not have (section 1). The port:

- Field operations become calls into a module `field` (`fe_add`, `fe_sub`, `fe_mul`,
  `fe_sq`, `fe_inv`, `fe_lit`, `fe_from_bytes`, `fe_to_bytes`). In Rust, this module wraps
  hacspec's `nat_mod` type, so the port runs. Charon treats it as opaque.
- The scalar is kept as its masked bytes, and a bit read replaces `k.bit(i)`.
- The ladder loop is tail recursion, because Aeneas fails on the loop form over a tuple
  state (Aeneas issue #1459).

`point_add_and_double` in the port matches the spec line for line, with `pow(2)` written
as `fe_sq` and `from_literal` as `fe_lit`. In Lean, the field module is written by hand
over `ZMod (2^255 - 19)` (`lean/X25519Ref/FunsExternal.lean`, section 4).

Real. The real code is the copy of curve25519-dalek in
[`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify).
It differs from upstream 4.2.0 by 361 changed lines that make the code extractable: loops
become `while` loops, some `debug_assert!`s are removed, and the ladder `mul` avoids
iterator adapters. On the step's path, the changes touch `pow2k`, which `square` calls,
and `add_assign`, which `add` calls. The shared library holds one extraction of this copy
for tracks B and D. Charon starts from the entry points of both tracks. For this track,
they are `differential_add_and_double`, `mul_clamped`, `MontgomeryPoint::to_bytes` and
`MontgomeryPoint::as_bytes`. The definitions on the path of `x25519` have the same text as
in the earlier extraction from the first three entry points alone. The Lean side needs one shadowing
fix in `Funs.lean`, in `mul`, outside the step. `shared/dalek/extract.sh` applies it as a
patch to the clean Aeneas output. The paths also need 10 hand definitions for `subtle` and
`zeroize` (section 4). Six come from `curve25519-dalek-lean-verify`, and four from track D.

Real wrapper. `real-x25519/` holds x25519-dalek 2.0.1 from crates.io, with no source edits.
Its `Cargo.toml` makes x25519-dalek use the curve25519-dalek copy above, and its
`.cargo/config.toml` sets the same backend. The extraction turns on the features
`static_secrets` and `reusable_secrets`. Charon starts from 12 items: `x25519`,
`X25519_BASEPOINT_BYTES`, `diffie_hellman` on the three secret types, the six accessors and
`SharedSecret::was_contributory` (`extract-real.sh`). The curve25519-dalek functions that
they call belong to another crate, so Charon leaves them opaque. Aeneas declares them as
axioms in `FunsExternal_Template.lean`. `lean/X25519Dalek/FunsExternal.lean` replaces the
axioms: it imports `Curve25519Dalek.Funs` of the shared library, which defines `mul_clamped`,
`MontgomeryPoint::to_bytes`, `MontgomeryPoint::as_bytes`, `FieldElement51::from_bytes`, the
`ct_eq` of `FieldElement51` and the `subtle` conversion from `Choice` to `bool` with the same
names. `lean/X25519Dalek/TypesExternal.lean` does the same for the opaque types
`FieldElement51` and `subtle::Choice`. The proofs rewrite with the specs of the shared
library, so they fail if a name binds to another declaration.

`was_contributory` calls the blanket `is_identity` of curve25519-dalek, with the
`ConstantTimeEq` and `Identity` impls of `MontgomeryPoint`. Their Lean definitions take the
trait structures that `Types.lean` of this extraction declares, so the shared library cannot
supply them. The script passes `--include` for these three functions, so Charon translates
their bodies from the curve25519-dalek copy into this extraction. Thus no definition on the
path is written by hand, beyond those of the shared library.

`EphemeralSecret` erases its bytes on drop (feature `zeroize`). Charon reaches its `Drop`
impl, and with it the `zeroize` functions of the `zeroize` crate. Aeneas does not call the
`Drop` impl from `diffie_hellman`, so the extraction keeps it opaque (`--opaque`), and its
axiom stays in the template. No Lean definition uses it.

The generated `Types.lean` defines `MontgomeryPoint` as `Array U8 32#usize`, as
`Curve25519Dalek.Types` does. It translates the newtypes `StaticSecret`, `PublicKey` and
`SharedSecret` to the same array. So the `From<[u8; 32]>` impls of `StaticSecret` and
`PublicKey`, whose bodies are the tuple constructors, are the identity in Lean, and the
theorems take bytes for these types. Charon cannot start from a method of a generic trait
impl such as `From<[u8; 32]>` or `AsRef<[u8]>` ("does not support trait generics"), so the
two `from` functions and the three `as_ref` functions are not in the extraction. A start from the whole `x25519` module adds 28
opaque functions (random number generation, `Debug`, `Hash` and others) as axioms to the
Lean project. The track admits no axioms beyond the standard three, so it does not do that.
Section 4 lists the `from` step as a source correspondence.

Field proofs. `curve25519-dalek-lean-verify` proves the field operations on Aeneas
`6e167c9b`. This track uses `d119a474`. The proofs are ported in
`shared/dalek/lean/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/`:

| File | `curve25519-dalek-lean-verify` lines | Port lines | `diff` lines | Change |
|---|---|---|---|---|
| `Reduce` | 105 | 208 | 205 | New proof, in two stages, with the arithmetic in one lemma |
| `Sub` | 166 | 144 | 52 | New last part. The offsets add up to `16 * p` |
| `Pow2K` | 902 | 885 | 197 | Fold lemmas, an unfolding equation, a new carry stage proof |
| `Mul` | 957 | 948 | 191 | The same changes as `Pow2K` |
| `AddAssign` | 83 | 90 | 9 | One `grind` call replaced |
| `Add`, `Square` | | | 0 | None |
| `CarryBlock` | new | 68 | new | One carry block, shared by `Pow2K` and `Mul` |

`Auxiliary.lean` also changed in three proofs. Each changed file has a "Port note" in its
header. The statements of the spec theorems did not change.

Byte and inversion proofs. The full theorem also uses four more specs, ported in
`shared/dalek/lean/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/` and
`shared/dalek/lean/Curve25519Dalek/Specs/Field/FieldElement51/`:

| File | `curve25519-dalek-lean-verify` lines | Port lines | `diff` lines | Change |
|---|---|---|---|---|
| `FromBytes` | 270 | 281 | 25 | Index bounds stated before `step*`. No more `maxHeartbeats 1000000` |
| `ToBytes` | 711 | 1018 | 1117 | New proof of `to_bytes_spec` in eight parts. No more `maxHeartbeats 1600000`. Ten `bv_decide` proofs replaced |
| `Pow22501`, `Invert` | 125, 81 | 125, 81 | 0 | None |

Upstream `to_bytes_spec` steps through the whole function at once. The port splits
`to_bytes` into three stages: the carry chain that computes `q`, the carry chain that
gives five canonical limbs, and the packing into bytes. The packing has five parts, one per
limb boundary. An unfolding lemma proves that the parts compose to `to_bytes`. The
`bv_decide` tactic adds axioms that trust native code, so the port proves those lemmas with
`omega` and `Nat` bit lemmas.

## 3. Statement

The main theorem is `X25519Sim.x25519_refines` (`lean/Sim/X25519.lean`):

```lean
theorem x25519_refines (k u : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k u ⦃ r =>
      x25519_ref.x25519_scalarmult k u = ok r ⦄
```

`⦃ ⦄` is the Aeneas total-correctness triple. The theorem has no premises. For every
32-byte scalar `k` and u-coordinate `u`, the real function returns a value with no panic,
no overflow and no divergence. The reference returns the
same 32 bytes. The relation on inputs and outputs is equality of bytes.

The theorem for the call that libsignal makes is
`X25519Sim.static_diffie_hellman_as_bytes_refines` (`lean/Sim/X25519.lean`). Here `s` is
the 32 bytes that the stored `StaticSecret` wraps, and `u` is the argument of
`PublicKey::from` (section 4, source correspondence):

```lean
theorem static_diffie_hellman_as_bytes_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.StaticSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.as_bytes ss) ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄
```

`X25519Sim.static_diffie_hellman_refines` states the same for `diffie_hellman` alone.
`ephemeral_diffie_hellman_refines` and `reusable_diffie_hellman_refines` state it for the
other two secret types. `x25519_basepoint_refines` states that
`x25519 k X25519_BASEPOINT_BYTES` returns the result of `x25519_secret_to_public k`.

The all-zero check is `X25519Sim.static_diffie_hellman_was_contributory_refines`
(`lean/Sim/Contributory.lean`), with the same statement for `EphemeralSecret` and
`ReusableSecret`. The real side computes the shared secret and then `was_contributory`.
The reference side computes `K = x25519_scalarmult s u` and then our check
`x25519_is_all_zero K`. The real result is the negation of the reference check:

```lean
theorem static_diffie_hellman_was_contributory_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.StaticSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let k ← x25519_ref.x25519_scalarmult s u
        let z ← x25519_ref.x25519_is_all_zero k
        ok (!z)) = ok b ⦄
```

The layer below is `X25519Sim.mul_clamped_refines` (`lean/Sim/Full.lean`). It states the
same for `MontgomeryPoint::mul_clamped`, with the arguments in the other order:

```lean
theorem mul_clamped_refines (u s : Array U8 32#usize) :
    montgomery.MontgomeryPoint.mul_clamped u s ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄
```

The theorems relate two Aeneas translations. The real side is x25519-dalek 2.0.1 on the
`curve25519-dalek-lean-verify` copy of dalek, built with the serial u64 backend
(`real-dalek/.cargo/config.toml`). The
reference side is the plain-Rust port with the `ZMod p` field model. The theorems rest on
the trusted definitions of section 4.

Inside the proof, a relation maps a real field element to the reference field. `toZ` is
in `lean/Sim/Pilot.lean`, and the limb bound `Bnd` is in
`shared/dalek/lean/DalekSim/Basic.lean`. `FE` is `FieldElement51`:

```lean
def toZ (f : FE) : _root_.field.Fe := ((Field51_as_Nat f : Nat) : ZMod p)
def Bnd (k : Nat) (f : FE) : Prop := ∀ i < 5, (f[i]!).val < 2 ^ k
```

A `FieldElement51` has five 64-bit limbs. `Field51_as_Nat` reads them in radix `2^51`, and
`toZ` reduces the result mod `p = 2^255 - 19`. `Bnd k f` states that every limb is below
`2^k`.

The ladder step layer is `X25519Sim.differential_add_and_double_refines_proved`
(`lean/Sim/Discharge.lean`). `mul_loop_spec` applies it once per ladder iteration:

```lean
theorem differential_add_and_double_refines_proved
    (P Q : montgomery.ProjectivePoint) (u : FE)
    (hPU : Bnd 53 P.U) (hPW : Bnd 53 P.W) (hQU : Bnd 53 Q.U) (hQW : Bnd 53 Q.W)
    (hu : Bnd 54 u) (z1 : _root_.field.Fe) :
    montgomery.differential_add_and_double P Q u ⦃ r =>
      ∃ s, x25519_ref.point_add_and_double (toZ u, z1)
              ((toZ P.U, toZ P.W), (toZ Q.U, toZ Q.W)) = ok s ∧
        toZ r.1.U = s.1.1 ∧ toZ r.1.W = s.1.2 ∧
        toZ r.2.U = s.2.1 ∧ toZ r.2.W = s.2.2 ∧
        Bnd 52 r.1.U ∧ Bnd 52 r.1.W ∧ Bnd 52 r.2.U ∧ Bnd 52 r.2.W ⦄
```

Under limb bounds on the inputs, the real step returns a value with no panic, no overflow and no divergence. The reference step on
the mapped inputs also returns a value. The four output coordinates are equal under `toZ`,
and every output limb is below `2^52`. The output bound implies the input bounds, so the
invariant carries from one step to the next. The reference step does not read the `z`
coordinate of the base point, so `z1` is arbitrary.

The step theorem is a corollary of `differential_add_and_double_refines` (`lean/Sim/Pilot.lean`),
which takes the four field contracts `C : FieldContracts` as a premise.
`field_contracts` (`lean/Sim/Discharge.lean`) proves the four contracts from the ported
`add_spec`, `sub_spec`, `mul_spec` and `square_spec`. `FieldContracts` is stated in
`Pilot.lean`, which does not import the spec files, and the kernel checks that the
statements agree.

## 4. Assumptions

Premises. The full theorems have none. The step theorem has limb bounds: every limb of the
four point coordinates is below `2^53`, and every limb of `u` is below `2^54`. The full
theorem discharges them, because the ladder keeps every limb below `2^52`.

Trusted definitions. `#print axioms` does not show them.

1. The port to plain Rust computes the same as the hacspec spec. Its Rust tests pass the
   RFC 7748 vectors of sections 5.2 and 6.1, with hacspec's `nat_mod` field (section 6).
   Our addition `x25519_is_all_zero` computes the check of RFC 7748, section 6.1. This
   rests on review of its 9 lines and on its tests.
2. The Lean field model computes the same as hacspec's `nat_mod`. `field.Fe` is
   `ZMod (2^255 - 19)` (`lean/X25519Ref/TypesExternal.lean`). `fe_add`, `fe_sub`, `fe_mul`
   and `fe_sq` are the ring operations. `fe_inv` is the `ZMod` inverse, which maps 0 to 0
   as `nat_mod`'s `inv` does. `fe_from_bytes` decodes little-endian and reduces mod p.
   `fe_to_bytes` encodes the canonical representative. The ladder step uses only the ring
   operations and `fe_lit`. The full theorems also use `fe_inv`, `fe_from_bytes` and
   `fe_to_bytes`.
3. The 10 hand definitions for `subtle` and `zeroize` on the real side: 9 functions in
   `shared/dalek/lean/Curve25519Dalek/FunsExternal.lean` and the type `subtle.Choice` in
   `shared/dalek/lean/Curve25519Dalek/TypesExternal.lean`. The step does not use them. The
   ladder uses 5 functions and the type, from `curve25519-dalek-lean-verify`. The
   `was_contributory` theorems also use 4 functions that track D wrote: the conversion
   from `Choice` to `bool`, the `ct_eq` of `u8`, and the slice `ct_eq` with its loop. A
   `Choice` carries a proof that its value is 0 or 1. Every `Choice` that the paths build
   has this property, and the proof shows it. `conditional_select`
   returns `b` if the choice is 1 and `a` otherwise. Rust computes the same with a bit mask,
   in constant time, and the mask is correct only for 0 and 1. `conditional_swap` calls
   `conditional_assign` twice, as the Rust default method does. `subtle.Choice.from`
   panics on inputs other than 0 and 1, where Rust has only a `debug_assert!`. `zeroize`
   returns the default value. Its result is not used. The `ct_eq` of `u8` returns 1 iff
   the two bytes are equal, and the slice `ct_eq` returns 1 iff the slices are equal.
   Rust computes both with bit operations in constant time.
4. The real code is the modified copy of dalek in `curve25519-dalek-lean-verify`, and
   x25519-dalek 2.0.1. The theorems hold for that code.

Source correspondence. Two conversions that libsignal uses are not in the extraction.
`StaticSecret::from` runs when libsignal builds the key, and `PublicKey::from` runs in
`calculate_agreement`. Section 2 gives the reason. The `From<[u8; 32]>` impls of `StaticSecret` and `PublicKey` are the
tuple constructors `StaticSecret(bytes)` and `PublicKey(MontgomeryPoint(bytes))`, in
x25519-dalek 2.0.1 and, with the same text, in 3.0.0 (`compare-dalek5.py`). Aeneas
translates the three newtypes to `Array U8 32#usize`, so these impls are the identity on
the arguments of the theorems. This rests on review of the Rust source, not on a proof.

Axioms. `lake env lean Sim/AxiomsDischarge.lean` gives only `propext`, `Classical.choice`
and `Quot.sound` for the step theorem, for `field_contracts` and for each contract.
`lake env lean Sim/AxiomsFull.lean` gives the same three for `mul_clamped_refines`, the
ported `from_bytes_spec`, `to_bytes_spec` and `invert_spec`, and every theorem of
`Sim/X25519.lean` and `Sim/Contributory.lean` that this README names.
`lake env lean Sim/AxiomsBridge.lean` gives the same three for `toU_dblY` and
`toU_dblY_curve25519`, and only `propext` and `Quot.sound` for `dadd_core` (section 5). It
gives the three standard axioms for the ladder theorems of `Sim/EdwardsLadder.lean` and
`Sim/BaseLadder.lean`, from `dbl_rep` to `mul_basepoint_spec`, and for the base point facts
`basePoint_y`, `basePoint_x_even` and `toU_basePoint`. The
axioms of `X25519Dalek/FunsExternal_Template.lean` are not in the Lean project, so the
theorems cannot depend on them.

## 5. Proof structure

The full proof has seven files besides the step layer (`Pilot.lean`, `Discharge.lean`) and
the ported field specs:

| File | Lines | Content |
|---|---|---|
| `Sim/LadderMath.lean` | 199 | The ladder as a pure function over any commutative ring. The scaling invariant `Rel`, the case `u = 0`, and `enc_ladder_extra_step` over a field |
| `Sim/RefSide.lean` | 117 | The reference `scalar_bit`, `ladder_step`, `ladder_loop`, `montgomery_ladder` and `encode_point` in closed form |
| `Sim/Bytes.lean` | 53 | `fe_to_bytes` and `fe_from_bytes` against `U8x32_as_Nat`, in both directions for `fe_to_bytes`. The base-256 digits and the top-bit mask are in `shared/dalek/lean/DalekSim/Bytes.lean` |
| `Sim/RealSide.lean` | 245 | `conditional_select`, `conditional_swap`, the bit read with `Isize` operations, and `mul_loop_spec` |
| `Sim/Full.lean` | 227 | Clamping, decoding, `as_affine`, dalek's `mul`, and `mul_clamped_refines` |
| `Sim/X25519.lean` | 125 | `x25519_refines`, the `diffie_hellman` theorems, the accessors and the base point, from `mul_clamped_refines`, `to_bytes` and `as_bytes` |
| `Sim/Contributory.lean` | 201 | The loop of `x25519_is_all_zero`, `ct_eq` and `was_contributory` over `ZMod p`, the canonical output of `x25519_scalarmult`, and the three `was_contributory` theorems |

The limb bound `Bnd`, `bnd_mono` and the `Result` lemmas `exists_ok_of_spec` and
`eq_ok_of_spec` do not depend on the reference. They are in
`shared/dalek/lean/DalekSim/Basic.lean`, which track D also uses. The slice and field
`ct_eq` lemmas and the byte lemmas that `Sim/Contributory.lean` uses are in
`shared/dalek/lean/DalekSim/Choice.lean` and `Bytes.lean`, shared with track D.

`Sim/EdwardsBridge.lean` (136 lines), `Sim/EdwardsLadder.lean` (269 lines) and
`Sim/BaseLadder.lean` (145 lines) are steps toward a proof of public-key derivation
(`PublicKey::from`). They are not part of the proofs above. dalek computes the public key on
the Edwards curve and maps it to the Montgomery u-coordinate `(1 + y) / (1 - y)`, but the
reference uses the Montgomery ladder. `toU_dblY` shows that this map sends the affine
Edwards double of a point to the encoding of the ladder doubling `dbl`.
`toU_dblY_curve25519` is its instance for Curve25519, with the curve equation as the only
premise. `dadd_core` is the identity behind the differential addition, with the
denominators multiplied out. `dbl_key` and `dbl_factor_ne_zero` are the doubling identities
that `toU_dblY` and `dbl_rep` share. The Curve25519 constant `d` and its two facts are in
`shared/dalek/lean/DalekSim/Edwards.lean`.

`Sim/EdwardsLadder.lean` proves that the ladder computes multiples in the Edwards group
`Point d` of `DalekSim/Edwards.lean`. The Edwards point `(x, y)` has the projective point
`rep (x, y) = (1 + y : 1 - y)`, and the identity has `rep = (2 : 0)`. `dbl_rep` and
`dadd_rep` equate projective points up to a nonzero factor, not only encodings. `dadd_rep`
needs `u (1 - y_D) = 1 + y_D` for the y-coordinate `y_D` of the difference, and `u ≠ 0`.
With `u ≠ 0`, these hypotheses hold exactly when `u = toU y_D`. Both the identity and
`(0, -1)` have `toU = 0`, so these hypotheses exclude `P = Q` and
`P - Q = (0, -1)`. The ladder keeps the
difference equal to `B`, so the invariant `ladder_rep` has no exceptional state. A state
can hold the identity, or two points that are negatives of each other. Only the final
encoding uses `a⁻¹ = 0`, where `toU` of the identity is 0. `basePoint` is the edwards25519
base point, and `toU_basePoint` shows that its u-coordinate is 9.
`enc_ladder_nine` states: the ladder at `u = 9` over a list of bits returns `toU` of
`m • basePoint`, where `m` is the number of the bits. `Sim/BaseLadder.lean` reads the bits of
a 32-byte scalar. `enc_ladder_nine_clamped` covers a scalar with bit 255 cleared, as after
clamping, with `m = U8x32_as_Nat k`. `mul_basepoint_spec` states the same for dalek's
`&MontgomeryPoint * &Scalar` on `X25519_BASEPOINT_BYTES`.

A proof of `PublicKey::from` needs more:

1. dalek adds and doubles in extended coordinates. `dblY` and `add` are affine formulas.
2. With the feature `precomputed-tables`, `mul_base_clamped` multiplies with a radix-16
   table of multiples of the base point, not with a ladder.
   `shared/dalek/lean/DalekSim/BasepointTable.lean` proves that entry `j` of row `i` of the
   table encodes `[(j + 1) 256^i] B` in `Point dEd`. A proof must still show that `mul_base`
   computes `k • B` from these entries. `enc_ladder_nine_clamped` then gives the ladder side.
3. No theorem links `dEd` to dalek's `EDWARDS_D`, or `basePoint` to
   `ED25519_BASEPOINT_POINT`. Track D proves the first link for its own copy of the constant
   (`edwards_d_spec`). `B` of `BasepointTable.lean` and `basePoint` have the same
   coordinates, but no theorem equates them yet.
4. `EdwardsPoint::to_montgomery` maps the extended point `(X : Y : Z : T)` to
   `(Z + Y) / (Z - Y)`. A proof must show that this is `toU y` of the affine point.

`mul_loop_spec` is an induction on the number of remaining bits. The loop body reads a bit,
swaps, calls the step theorem and recurses. A fold lemma, `mul_loop_unfold`, moves the bit
read into a separate function, `read_bit`, with its own spec. That spec needs one lemma on
`Isize`: `i &&& 7 = i % 8` for `0 ≤ i ≤ 254`. The lemma holds on 32-bit and 64-bit
platforms. The reference loop is tail recursion, and `ladder_loop_eq` is an induction of
the same shape. The math in `LadderMath.lean` uses no Aeneas definitions.

The ladder step layer, `Pilot.lean` (201 lines), has three parts:

1. Lockstep. 19 `step with` calls, one per real field operation (18) and one for the
   constant `APLUS2_OVER_FOUR`. Each uses a contract restated over `toZ` (`add_z`,
   `sub_z`, `mul_z`, `square_z`).
2. Bounds. 21 goals of the form `exact bnd_mono h (by norm_num)`. The bounds were chosen
   by hand: 53 for `add`, 63 or 54 for `sub`, 54 for `mul` and `square`.
3. Representation. `point_add_and_double_eq` computes the reference step in closed form.
   Four ring identities in `ZMod p` close the output goals. One needs `AA = BB + E`, because
   dalek computes `z2` as `E * (121666 E + BB)` and RFC 7748 as `E * (AA + 121665 E)`.

In the step, the two control flows match call for call at the level of field operations.
This does not extend to the ladder, which needs the invariant above.

No proof sets `maxHeartbeats`. Two carry stages of `curve25519-dalek-lean-verify` used
about 335,000 heartbeats on our pin, above the default 200,000. They now step over three
calls to `carry_block`, with its own spec, and use about 55,000. The largest proof in the
track, `mul_product_stage_spec`, uses 151,845. The new files and the four newly ported
specs build with a limit of 151,845. Some proofs set `maxRecDepth 4096`.

## 6. Checks

1. `lake build` in `lean/` passes. No file in `lean/Sim/` or
   `shared/dalek/lean/Curve25519Dalek/` has a `sorry`.
2. `Sim/Axioms.lean`, `Sim/AxiomsDischarge.lean`, `Sim/AxiomsFull.lean` and
   `Sim/AxiomsBridge.lean` check the axiom lists of section 4 with `#guard_msgs`.
   `lake build` builds them (target `Checks`), and the build fails if a list changes.
3. `cargo test` in `ref-plain/` passes the RFC tests and the edge tests of
   `tests/edge.rs`. The RFC tests are the two vectors of RFC 7748, section 5.2, the
   iterated test of section 5.2 after 1 and 1,000 iterations, and all values of section
   6.1: both public keys and the shared secret from both sides. A test of
   `x25519_is_all_zero` checks 32 zero bytes and each byte set alone. The test after
   1,000,000 iterations is marked `#[ignore]`, because it runs for hours. The tests build
   with `opt-level = 3`. The edge inputs are the low-order points 0, 1, `p - 1`, `p`, `p + 1` and
   a point of order 8, the values `p + 9` and `2^255 - 1` above `p`, a u-coordinate with bit
   255 set, and a scalar with the clamped bits changed. Three fixed outputs agree with
   OpenSSL's X25519.
4. `Sim/RefVectors.lean` runs the Lean reference, with the `ZMod` model, on the same RFC
   vectors and edge inputs, with `#guard`. It also runs `x25519_is_all_zero` on the shared
   secret of section 6.1 and on two other inputs. `lake build` builds it, and the build fails if
   an output differs. This trusts the Lean compiler, and it is a test, not a proof.
5. `scripts/check-short-names.py` finds no name in `lean/X25519Ref`,
   `shared/dalek/lean/Curve25519Dalek` and `lean/X25519Dalek` that Lean binds to a different
   declaration from the crate-level one (Aeneas issue #1458). It reads declarations with the name on the line of the keyword
   or on a later line, after blank and comment lines. It fails on a keyword whose name it
   cannot read. `scripts/tests/test-check-short-names.sh` tests both cases.
6. `compare-dalek5.py` checks 88 items, among them the proved path, against
   curve25519-dalek 5.0.0 and x25519-dalek 3.0.0 (section 1). It fails on a missing or
   ambiguous item and on any difference other than the reviewed ones. With `--self-test`,
   it changes each item of the 5.0.0 and 3.0.0 trees in memory and checks that the
   comparison reports the change.
7. `shared/dalek/check.sh` makes sure that the Lean files of the shared library are the
   Aeneas output in `shared/dalek/extract/` with the patches of the library, and it builds
   the library.
8. `check.sh` makes sure that `Funs.lean` and `Types.lean` in `lean/X25519Ref` and
   `lean/X25519Dalek` are the same as the Aeneas output in `ref-plain/Ref` and
   `real-x25519/X25519`. With `REPLAY_EXTRACTION=1`, it also runs `extract-real.sh --check`,
   which extracts x25519-dalek again and fails if the output differs from
   `real-x25519/X25519`. `shared/dalek/check.sh` then also extracts the shared library again.

`check.sh` runs all eight checks, check 7 first, and stops at the first failure.

## 7. Strengths and weaknesses

Strengths:

1. The track proves full refinement for x25519-dalek's `x25519` and the three
   `diffie_hellman` methods against `x25519_scalarmult`, for `X25519_BASEPOINT_BYTES` and
   the accessors, and for `was_contributory` against our all-zero check. The theorems have
   no premises, and the axioms are only the standard three. With the source
   correspondence of section 4, `static_diffie_hellman_as_bytes_refines` covers the call
   of libsignal's `calculate_agreement`.
2. No primitive is opaque. Both sides reduce to arithmetic mod p.
3. The ladder step is the cleanest lockstep of the three tracks. The two sides match
   operation for operation.
4. The relation is total, and the output bound carries to the next step.
5. The Lean reference reproduces the RFC 7748 test vectors, with the iterated test up to
   1,000 iterations, and the outputs of the Rust port on the edge inputs of
   `ref-plain/tests/edge.rs`.
6. The proved path below `mul_clamped` is the code of libsignal's X25519 agreement in
   builds with the serial u64 field backend, apart from the extraction edits (section 1).
7. The ladder argument is pure algebra over a ring. The Aeneas parts of the proof only
   connect each program to it.

Weaknesses:

1. The ladder needed a hand-written invariant and a scaling argument. No generic lockstep
   rule produces them.
2. The reference is a port, and the field model is hand-written. Their faithfulness rests
   on review, on the RFC vectors and on the edge inputs of `ref-plain/tests/edge.rs`.
3. The real code is a modified copy of dalek. The theorems cover upstream dalek only if
   the 361-line diff preserves meaning.
4. The field proofs are ports of another project's proofs. Every Aeneas update can break
   them again, because they depend on the goal shapes after `step*`.
5. The theorems do not cover key generation, `PublicKey::from(&secret)` with
   `mul_base_clamped`, or the trait impls of x25519-dalek (section 1, "Gaps: RFC 7748, the
   reference and x25519-dalek"). The two `From<[u8; 32]>` impls on the call of
   libsignal are not extracted. Their link to the theorems rests on review (section 4,
   source correspondence). They also do not cover the constant-time behavior of the real
   code or the erasure of secrets.
6. The hacspec reference misses two parts of RFC 7748, section 6.1: key generation and
   the check for the all-zero shared secret. The theorem for `was_contributory` is against
   our addition to the reference, which only review and tests link to the RFC. Key
   generation is not covered. The reference has none, and the extraction does not model
   the RNG.
7. The proved x25519-dalek is 2.0.1. libsignal uses 3.0.0, whose 14 items on the proved
   paths have the same text but build on curve25519-dalek 5.0.0. 3.0.0 has different drop
   and zeroize code for the secret types, and the track does not extract it (section 1).

## 8. Reproduce

From the repository root, run `scripts/fetch-upstreams.sh` once. The comparison needs
curve25519-dalek 5.0.0 and x25519-dalek 3.0.0 in the cargo registry, for example after
`cargo fetch` in a project that depends on `curve25519-dalek = "=5.0.0"` and
`x25519-dalek = "=3.0.0"`. Then run every check:

```bash
tracks/x25519/check.sh
```

To skip the comparison, set `SKIP_DALEK5=1`. To use other copies of the two crates, set
`DALEK5` and `X25519_DALEK3` to their directories.

The extraction commands for the reference. Run them in `ref-plain/`, with the Aeneas
release of `.aeneas/` on `PATH`:

```bash
charon cargo --preset=aeneas --start-from crate::x25519_scalarmult --start-from crate::x25519_secret_to_public --start-from crate::point_add_and_double --start-from crate::x25519_is_all_zero --opaque crate::field
aeneas -backend lean -split-files -loops-to-rec -max-heartbeats 200000 -namespace x25519_ref -dest Ref x25519_ref.llbc
```

For x25519-dalek, `extract-real.sh` holds the commands. It writes to `real-x25519/X25519/`.
With `--check`, it extracts into a temporary directory and fails if the output differs.
`check.sh` runs it in that mode if `REPLAY_EXTRACTION=1`:

```bash
tracks/x25519/extract-real.sh
```

The script passes `--remap-path-prefix` to rustc, so that the `Source:` paths of the
curve25519-dalek items are relative to the repository root. The paths of the x25519-dalek
items are relative to `real-x25519/`.

`lean/X25519Ref` and `lean/X25519Dalek` hold copies of `ref-plain/Ref` and
`real-x25519/X25519` without hand edits, plus the hand-written files
`X25519Ref/TypesExternal.lean`, `X25519Ref/FunsExternal.lean` and
`X25519Dalek/FunsExternal.lean` (sections 2 and 4).
`shared/dalek/extract.sh` replays the extraction of curve25519-dalek and applies the hand
edit of section 2 (`shared/dalek/README.md`, section 1).

`check.sh` and the shared library share build directories with track D. `check.sh` takes a
lock, so a second check waits. Do not run `lake build` by hand in both tracks at the same
time.
