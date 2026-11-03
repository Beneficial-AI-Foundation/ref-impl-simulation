# Track B: X25519 (RFC 7748)

Track B proves full refinement for two functions of x25519-dalek against one reference
function. For every 32-byte scalar and u-coordinate, x25519-dalek's `x25519` returns
without panic, overflow or divergence, and the reference `x25519_scalarmult` returns the
same 32 bytes. The theorem is `X25519Sim.x25519_refines` (section 3). The same holds for
`StaticSecret::diffie_hellman`, the function that libsignal calls, followed by
`SharedSecret::as_bytes` (`X25519Sim.static_diffie_hellman_as_bytes_refines`). The theorems
have no premises and use only the three standard axioms. Both functions call
curve25519-dalek's `MontgomeryPoint::mul_clamped`, and `X25519Sim.mul_clamped_refines`
proves the same result for that function. The other public functions of the reference and
of x25519-dalek are not covered. Section 1 lists them, with the gaps between RFC 7748, the
reference and x25519-dalek.

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
5.0.0 (libsignal `fc90b90f`). `calculate_agreement` computes
`StaticSecret::from(s).diffie_hellman(&PublicKey::from(u)).as_bytes()`. `diffie_hellman`
calls `MontgomeryPoint::mul_clamped`. libsignal does not call `x25519_dalek::x25519`.
x25519-dalek 3.0.0 needs curve25519-dalek 5, so the track extracts x25519-dalek 2.0.1, which
builds on the 4.2.0 copy. `compare-dalek5.py` compares 35 functions and constants on the
paths of the full theorems: 30 items of curve25519-dalek 5.0.0 against the copy proved
here, and 5 items of x25519-dalek 3.0.0 against 2.0.1 (`x25519`,
`StaticSecret::diffie_hellman`, `SharedSecret::as_bytes` and the two `From<[u8; 32]>`
impls of `StaticSecret` and `PublicKey`). It finds each item by its `impl` block and its
name, and fails if an item is missing or ambiguous. The crate checksums of 5.0.0 and 3.0.0
match libsignal's `Cargo.lock`. After comments and blank lines are removed, 31 items are
identical, the 5 items of x25519-dalek among them. Four items differ through three
extraction edits, and the script fails on any other difference:

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
`bits_le`, the multiplication wrappers and the 5 items of x25519-dalek. The script does not
compare the struct definitions. In both versions, `StaticSecret` wraps `[u8; 32]`, and
`PublicKey` and `SharedSecret` wrap a `MontgomeryPoint`.

The comparison covers libsignal builds with the serial u64 field backend: every 64-bit
target, and the 32-bit Android targets, because libsignal's `java/build_jni.sh` sets
`curve25519_dalek_bits = "64"` there. It does not cover a build with the `fiat` backend or
with `curve25519_dalek_bits = "32"`. libsignal builds dalek with
`overflow-checks = false` in release. The theorem shows that no arithmetic on the path
overflows, so this setting does not change the result.

### Layers of the full refinement

Full refinement here is a theorem about one API pair. It relates the real
`x25519_dalek::x25519` to the reference `x25519_scalarmult` on all 32-byte inputs. Both
functions take a scalar and a u-coordinate as bytes and return the result as bytes. The
table follows the call path from this pair down to the ladder step. The theorem
`X25519Sim.x25519_refines` (section 3) relates every pair in the table. The theorems for
`StaticSecret::diffie_hellman` share every layer below `mul_clamped`.

| Layer | Reference (`lean/X25519Ref`) | Real (`lean/X25519Dalek`, `shared/dalek/lean/Curve25519Dalek`) | Status | Lean |
|---|---|---|---|---|
| X25519 function | `x25519_scalarmult` | `x25519_dalek::x25519` | proved | `Sim/X25519.lean` |
| Shared secret | `x25519_scalarmult` | `StaticSecret::diffie_hellman`, then `SharedSecret::as_bytes` | proved | `Sim/X25519.lean` |
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
   steps.

The real side reuses specs of `curve25519-dalek-lean-verify` at commit `26d49052`:
`from_bytes`, `to_bytes`, `pow22501` and `invert`, ported to the Aeneas version of this
project (section 2). Its ladder spec, `mul_loop_spec`, has three `sorry`s at that commit,
so this track proves its own.

### Gaps: RFC 7748, the reference and x25519-dalek

Refinement is relative to the reference. A real function without a counterpart in the
reference is not covered, and the theorem says nothing about it. This section states the
gaps at three levels: what the RFC describes, what the hacspec reference has, and what
x25519-dalek 2.0.1 offers. It covers the Curve25519 part of the RFC.

| RFC 7748 | hacspec `curve25519` | x25519-dalek 2.0.1 | Status |
|---|---|---|---|
| Section 5: the function `X25519(k, u)`. Mask bit 255 of `u` (MUST), accept non-canonical `u` (MUST) | `x25519_scalarmult` | `x25519` | proved (`x25519_refines`). For the translated reference, `decode_point_spec` (`lean/Sim/Full.lean`) proves both MUST rules under the trusted field model: it reads `u` as `u mod 2^255` in `ZMod p`. That the unchanged hacspec spec and the field model match the RFC rests on review and tests |
| Section 6.1: the shared secret `X25519(a, K_B)` | `x25519_scalarmult` (no function of its own) | `diffie_hellman` on `EphemeralSecret`, `ReusableSecret`, `StaticSecret` | proved for `StaticSecret` (`static_diffie_hellman_refines`, and `static_diffie_hellman_as_bytes_refines` with `SharedSecret::as_bytes`). Not proved for `EphemeralSecret` and `ReusableSecret`. Each of their methods is one call to `mul_clamped`, which is proved, but the methods are not extracted |
| Section 6.1: the public key `X25519(a, 9)` | `x25519_secret_to_public` | `PublicKey::from(&secret)` for the three secret types | not proved. The real code goes through `EdwardsPoint::mul_base_clamped`, with precomputed base point tables if the feature `precomputed-tables` is on, and is not extracted |
| Section 6.1: the base point 9 | inside `x25519_secret_to_public` | `X25519_BASEPOINT_BYTES` | not proved |
| Section 6.1: Alice generates 32 random bytes | missing | `random_from_rng`, `random` (feature `getrandom`) and the deprecated `new` on the three secret types | not covered. The reference does not describe it, and functional refinement cannot state that bytes are random |
| Sections 6.1 and 7: check for the all-zero shared secret (MAY), for example by an OR of all bytes | missing | `SharedSecret::was_contributory` | not covered. dalek ignores bit 255 and compares with 0 mod p, so it also reports 0 for non-canonical encodings of 0. `SharedSecret` has no public constructor, and `diffie_hellman` returns canonical bytes, so this case does not occur through the API |
| Sections 6.1 and 7: a key-derivation function of `K`, `K_A` and `K_B`, and public keys bound into it | missing | missing | outside the track. The caller derives the symmetric key |
| Sections 5.1 and 7: side channels | not expressible | constant-time code through `subtle` | outside functional refinement |
| Sections 5.2 and 6.1: test vectors | some, in its tests | its tests | the track runs section 5.2 vector 1 and the section 6.1 test (section 6). It does not run vector 2, the iterated tests, or the other values of section 6.1 |
| Sections 4.2, 5 and 6.2: X448 | missing | missing | outside the track |

So the reference misses two parts of Curve25519 Diffie-Hellman in the RFC: key generation
and the all-zero check. It also has no X448. Key derivation is missing on both sides and is
left to the caller.

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
   private bytes. Of these, the theorems cover `SharedSecret::as_bytes` and, through the
   types, the two `From<[u8; 32]>` impls (section 2).
3. Traits: `PartialEq`, `Eq`, `Hash`, `Copy`, `Clone` and `Debug` on `PublicKey`, and
   `Clone` on `ReusableSecret` and `StaticSecret`. With the feature `zeroize`, all five
   types implement `Zeroize`, and the three secret types and `SharedSecret` also erase
   their bytes on drop. `PublicKey` does not. With the feature `serde`, `PublicKey` and
   `StaticSecret` implement `Serialize` and `Deserialize`. `PublicKey` equality ignores
   bit 255 and compares mod p, so two keys with different bytes can be equal. `Hash` uses
   the canonical bytes, so it agrees with this equality. The RFC defines no equality of
   keys.

The theorem also says nothing about constant time or about the erasure of secrets.

## 2. Translation

Both programs go through Charon and Aeneas. The Lake project `lean/` holds the reference,
the x25519-dalek wrapper and the proofs. It requires the shared library of curve25519-dalek
([`shared/dalek`](../../shared/dalek/README.md)).

Reference. Aeneas fails on the original spec, because of the supertraits of
`hacspec_lib::SeqTrait` (Aeneas issue #1164). The track uses a port to plain Rust
(`ref-plain/src/lib.rs`, 166 changed lines against the 110-line spec, plus the new
32-line `ref-plain/src/field.rs`). The unchanged spec, as a crate, is in `ref-hacspec/`.
The port:

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
they are `differential_add_and_double`, `mul_clamped` and `MontgomeryPoint::to_bytes`, which
`x25519` calls. The definitions on the path of this track have the same text as in the
earlier extraction from these three entry points alone. The Lean side needs one shadowing
fix in `Funs.lean`, in `mul`, outside the step. `shared/dalek/extract.sh` applies it as a
patch to the clean Aeneas output. The path also needs 6 hand definitions for `subtle` and
`zeroize` from `curve25519-dalek-lean-verify` (section 4).

Real wrapper. `real-x25519/` holds x25519-dalek 2.0.1 from crates.io, with no source edits.
Its `Cargo.toml` makes x25519-dalek use the curve25519-dalek copy above, and its
`.cargo/config.toml` sets the same backend. The extraction turns on the feature
`static_secrets`. Charon starts from `x25519`, `StaticSecret::diffie_hellman` and
`SharedSecret::as_bytes`. The three curve25519-dalek functions that they call,
`mul_clamped`, `to_bytes` and `as_bytes`, belong to another crate, so Charon leaves them
opaque. Aeneas declares them as axioms in `FunsExternal_Template.lean`.
`lean/X25519Dalek/FunsExternal.lean` replaces the axioms: it imports `Curve25519Dalek.Funs`
of the shared library, which defines the three functions with the same names. The proofs
rewrite with `mul_clamped_refines`, so they fail if a name binds to another declaration.

The generated `Types.lean` defines `MontgomeryPoint` as `Array U8 32#usize`, as
`Curve25519Dalek.Types` does. It translates the newtypes `StaticSecret`, `PublicKey` and
`SharedSecret` to the same array. So the `From<[u8; 32]>` impls of `StaticSecret` and
`PublicKey`, whose bodies are the tuple constructors, are the identity in Lean, and the
theorems take bytes for these types. Charon cannot start from a method of a generic trait
impl such as `From<[u8; 32]>` ("does not support trait generics"), so the two `from`
functions are not in the extraction. Starting from the whole `x25519` module brings 28
opaque functions (random number generation, `Debug`, `Hash` and others), each an axiom to
replace, so the track does not do that.

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
`StaticSecret::from(s)` and `u` is `PublicKey::from(u)` (section 2):

```lean
theorem static_diffie_hellman_as_bytes_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.StaticSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.as_bytes ss) ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄
```

`X25519Sim.static_diffie_hellman_refines` states the same for `diffie_hellman` alone.

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
reference side is the plain-Rust port with the `ZMod p` field model. The theorem rests on
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

Premises. The full theorem has none. The step theorem has limb bounds: every limb of the
four point coordinates is below `2^53`, and every limb of `u` is below `2^54`. The full
theorem discharges them, because the ladder keeps every limb below `2^52`.

Trusted definitions. `#print axioms` does not show them.

1. The port to plain Rust computes the same as the hacspec spec. Its Rust tests pass
   RFC 7748 section 5.2 vector 1 and section 6.1, with hacspec's `nat_mod` field.
2. The Lean field model computes the same as hacspec's `nat_mod`. `field.Fe` is
   `ZMod (2^255 - 19)` (`lean/X25519Ref/TypesExternal.lean`). `fe_add`, `fe_sub`, `fe_mul`
   and `fe_sq` are the ring operations. `fe_inv` is the `ZMod` inverse, which maps 0 to 0
   as `nat_mod`'s `inv` does. `fe_from_bytes` decodes little-endian and reduces mod p.
   `fe_to_bytes` encodes the canonical representative. The ladder step uses only the ring
   operations and `fe_lit`. The full theorem also uses `fe_inv`, `fe_from_bytes` and
   `fe_to_bytes`.
3. The 6 hand definitions for `subtle` and `zeroize` on the real side: 5 functions in
   `shared/dalek/lean/Curve25519Dalek/FunsExternal.lean` and the type `subtle.Choice` in
   `shared/dalek/lean/Curve25519Dalek/TypesExternal.lean`. The step does not use them. The
   full theorem uses all of them. A `Choice` carries a proof that its value is 0 or 1. Every `Choice`
   that the ladder builds has this property, and the proof shows it. `conditional_select`
   returns `b` if the choice is 1 and `a` otherwise. Rust computes the same with a bit mask,
   in constant time, and the mask is correct only for 0 and 1. `conditional_swap` calls
   `conditional_assign` twice, as the Rust default method does. `subtle.Choice.from`
   panics on inputs other than 0 and 1, where Rust has only a `debug_assert!`. `zeroize`
   returns the default value. Its result is not used.
4. The real code is the modified copy of dalek in `curve25519-dalek-lean-verify`, and
   x25519-dalek 2.0.1. The theorem holds for that code.

Axioms. `lake env lean Sim/AxiomsDischarge.lean` gives only `propext`, `Classical.choice`
and `Quot.sound` for the step theorem, for `field_contracts` and for each contract.
`lake env lean Sim/AxiomsFull.lean` gives the same three for `x25519_refines`,
`static_diffie_hellman_refines`, `static_diffie_hellman_as_bytes_refines`,
`mul_clamped_refines` and the ported `from_bytes_spec`, `to_bytes_spec` and
`invert_spec`. The axioms of `X25519Dalek/FunsExternal_Template.lean` are not in the Lean
project, so the theorems cannot depend on them.

## 5. Proof structure

The full proof has six files besides the step layer (`Pilot.lean`, `Discharge.lean`) and
the ported field specs:

| File | Lines | Content |
|---|---|---|
| `Sim/LadderMath.lean` | 191 | The ladder as a pure function over any commutative ring. The scaling invariant `Rel`, the case `u = 0`, and `enc_ladder_extra_step` over a field |
| `Sim/RefSide.lean` | 117 | The reference `scalar_bit`, `ladder_step`, `ladder_loop`, `montgomery_ladder` and `encode_point` in closed form |
| `Sim/Bytes.lean` | 38 | `fe_to_bytes` and `fe_from_bytes` against `U8x32_as_Nat`. The base-256 digits and the top-bit mask are in `shared/dalek/lean/DalekSim/Bytes.lean` |
| `Sim/RealSide.lean` | 245 | `conditional_select`, `conditional_swap`, the bit read with `Isize` operations, and `mul_loop_spec` |
| `Sim/Full.lean` | 227 | Clamping, decoding, `as_affine`, dalek's `mul`, and `mul_clamped_refines` |
| `Sim/X25519.lean` | 62 | `x25519_refines` and the two `diffie_hellman` theorems, from `mul_clamped_refines`, `to_bytes` and `as_bytes` |

The limb bound `Bnd`, `bnd_mono` and the `Result` lemmas `exists_ok_of_spec` and
`eq_ok_of_spec` do not depend on the reference. They are in
`shared/dalek/lean/DalekSim/Basic.lean`, which track D also uses.

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
2. `Sim/Axioms.lean`, `Sim/AxiomsDischarge.lean` and `Sim/AxiomsFull.lean` check the axiom
   lists of section 4 with `#guard_msgs`. `lake build` builds them (target `Checks`), and
   the build fails if a list changes.
3. `cargo test` in `ref-plain/` passes the two RFC tests and the edge tests of
   `tests/edge.rs`. The edge inputs are the low-order points 0, 1, `p - 1`, `p`, `p + 1` and
   a point of order 8, the values `p + 9` and `2^255 - 1` above `p`, a u-coordinate with bit
   255 set, and a scalar with the clamped bits changed. Three fixed outputs agree with
   OpenSSL's X25519.
4. `Sim/RefVectors.lean` runs the Lean reference, with the `ZMod` model, on the same RFC
   vectors and edge inputs, with `#guard`. `lake build` builds it, and the build fails if
   an output differs. This trusts the Lean compiler, and it is a test, not a proof.
5. `scripts/check-short-names.py` finds no name in `lean/X25519Ref`,
   `shared/dalek/lean/Curve25519Dalek` and `lean/X25519Dalek` that Lean binds to a different
   declaration from the crate-level one (Aeneas issue #1458). It reads declarations with the name on the line of the keyword
   or on a later line, after blank and comment lines. It fails on a keyword whose name it
   cannot read. `scripts/tests/test-check-short-names.sh` tests both cases.
6. `compare-dalek5.py` checks the proved path against curve25519-dalek 5.0.0 and
   x25519-dalek 3.0.0 (section 1). It fails on a missing or ambiguous item and on any
   difference other than the three reviewed edits. With `--self-test`, it changes each item
   of the 5.0.0 and 3.0.0 trees in memory and checks that the comparison reports the
   change.
7. `shared/dalek/check.sh` makes sure that the Lean files of the shared library are the
   Aeneas output in `shared/dalek/extract/` with the patches of the library, and it builds
   the library.
8. `check.sh` makes sure that `Funs.lean` and `Types.lean` in `lean/X25519Ref` and
   `lean/X25519Dalek` are the same as the Aeneas output in `ref-plain/Ref` and
   `real-x25519/X25519`.

`check.sh` runs all eight checks, check 7 first, and stops at the first failure.

## 7. Strengths and weaknesses

Strengths:

1. The track proves full refinement for x25519-dalek's `x25519` and
   `StaticSecret::diffie_hellman` against `x25519_scalarmult`. The theorems have no
   premises, and the axioms are only the standard three. The second theorem covers the
   call of libsignal's `calculate_agreement`.
2. No primitive is opaque. Both sides reduce to arithmetic mod p.
3. The ladder step is the cleanest lockstep of the three tracks. The two sides match
   operation for operation.
4. The relation is total, and the output bound carries to the next step.
5. The Lean reference reproduces two RFC test vectors and the outputs of the Rust port on
   the edge inputs of `ref-plain/tests/edge.rs`.
6. The proved path below `mul_clamped` is the code of libsignal's X25519 agreement in
   builds with the serial u64 field backend, apart from the extraction edits (section 1).
7. The ladder argument is pure algebra over a ring. The Aeneas parts of the proof only
   connect each program to it.

Weaknesses:

1. The ladder needed a hand-written invariant and a scaling argument. No generic lockstep
   rule produces them.
2. The reference is a port, and the field model is hand-written. Their faithfulness rests
   on review, on two RFC vectors and on the edge inputs of `ref-plain/tests/edge.rs`.
3. The real code is a modified copy of dalek. The theorem covers upstream dalek only if
   the 361-line diff preserves meaning.
4. The field proofs are ports of another project's proofs. Every Aeneas update can break
   them again, because they depend on the goal shapes after `step*`.
5. The theorems cover two functions only. They do not cover `x25519_secret_to_public`,
   `mul_base_clamped` or the other public functions of x25519-dalek (section 1, "Gaps: RFC
   7748, the reference and x25519-dalek"). The two `From<[u8; 32]>` impls on the call of
   libsignal are not extracted. The theorems rely on the translation of the newtypes to
   byte arrays (section 2). They also do not cover the constant-time behavior of the real
   code or the erasure of secrets.
6. The reference misses two parts of RFC 7748, section 6.1: key generation and the check
   for the all-zero shared secret. So no refinement theorem against it can cover
   `random_from_rng` or `was_contributory`.
7. The proved x25519-dalek is 2.0.1. libsignal uses 3.0.0, whose 5 compared items have
   the same text but build on curve25519-dalek 5.0.0.

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

The extraction commands. Run them in `ref-plain/` and in `real-x25519/`, with the Aeneas
release of `.aeneas/` on `PATH`:

```bash
charon cargo --preset=aeneas --start-from crate::x25519_scalarmult --start-from crate::x25519_secret_to_public --start-from crate::point_add_and_double --opaque crate::field
aeneas -backend lean -split-files -loops-to-rec -namespace x25519_ref -dest Ref x25519_ref.llbc
```

```bash
charon cargo --preset=aeneas --start-from 'x25519_dalek::x25519::x25519' --start-from 'x25519_dalek::x25519::StaticSecret::diffie_hellman' --start-from 'x25519_dalek::x25519::SharedSecret::as_bytes' -- --locked -p x25519-dalek --no-default-features --features alloc,zeroize,static_secrets --config "build.rustflags=[\"--remap-path-prefix=$(cd ../../.. && pwd)/=\"]"
aeneas -backend lean -loops-to-rec -split-files -dest X25519 x25519_dalek.llbc
```

The `--remap-path-prefix` flag makes the `Source:` paths of the generated files relative to
the repository root. Cargo adds it to the backend flags of `real-x25519/.cargo/config.toml`.

`lean/X25519Ref` and `lean/X25519Dalek` hold copies of `ref-plain/Ref` and
`real-x25519/X25519` without hand edits, plus the hand-written files
`X25519Ref/TypesExternal.lean`, `X25519Ref/FunsExternal.lean` and
`X25519Dalek/FunsExternal.lean` (sections 2 and 4).
`shared/dalek/extract.sh` replays the extraction of curve25519-dalek and applies the hand
edit of section 2 (`shared/dalek/README.md`, section 1).

`check.sh` and the shared library share build directories with track D. `check.sh` takes a
lock, so a second check waits. Do not run `lake build` by hand in both tracks at the same
time.
