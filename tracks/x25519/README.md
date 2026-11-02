# Track B: X25519 Montgomery ladder step (RFC 7748)

All paths are relative to `tracks/x25519/`.

## 1. Unit and sources

| Role | Code | Commit |
|---|---|---|
| Reference | `hacspec/specs` `curve25519/src/curve25519.rs`, old hacspec | `c511110d` (2025-04-22) |
| Reference library | `hacspec/hacspec` `lib/` | `4ecc847f` |
| Real | curve25519-dalek 4.2.0 as modified by `curve25519-dalek-lean-verify` | `26d49052` |

The unit is one step of the Montgomery ladder: the reference `point_add_and_double`
against the real `montgomery::differential_add_and_double`. Both whole ladders are
extracted too, but no theorem covers them. Scalar clamping, byte encoding and decoding,
field inversion and the X25519 API are out of scope.

libsignal computes X25519 through `x25519-dalek` 3.0.0 and curve25519-dalek 5.0.0. On
2026-10-30, against libsignal `fc90b90f`, `differential_add_and_double` in 5.0.0 was
textually identical to the version proved here. The field functions that it calls were
identical too, apart from the extraction edits in `pow2k` and `add_assign` (section 2).
These functions are `add`, `sub`, `mul`, `square` and `reduce`.

## 2. Translation

Both programs go through Charon and Aeneas into one Lake project (`lean/`).

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

Real. The real code is the copy of curve25519-dalek in `curve25519-dalek-lean-verify`.
It differs from upstream 4.2.0 by 361 changed lines that make the code extractable: loops
become `while` loops, some `debug_assert!`s are removed, and the ladder `mul` avoids
iterator adapters. On the step's path, the changes touch `pow2k`, which `square` calls,
and `add_assign`, which `add` calls. Charon starts from the Montgomery functions
(`--start-from`). The Lean side needs one shadowing fix in `Funs.lean`, in `mul`, outside
the step. It also needs 6 hand definitions for `subtle` and `zeroize` from `lean-verify`.

Field proofs. `lean-verify` proves the field operations on Aeneas `6e167c9b`. This track
uses `d119a474`. The proofs are ported in
`lean/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/`:

| File | `lean-verify` lines | Port lines | `diff` lines | Change |
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

## 3. Statement

The relation maps a real field element to the reference field (`lean/Sim/Pilot.lean`):

```lean
def toZ (f : FE) : _root_.field.Fe := ((Field51_as_Nat f : Nat) : ZMod p)
def Bnd (k : Nat) (f : FE) : Prop := ∀ i < 5, (f[i]!).val < 2 ^ k
```

A `FieldElement51` has five 64-bit limbs. `Field51_as_Nat` reads them in radix `2^51`, and
`toZ` reduces the result mod `p = 2^255 - 19`. `Bnd k f` states that every limb is below
`2^k`.

The main theorem is `X25519Sim.differential_add_and_double_refines_proved`
(`lean/Sim/Discharge.lean`):

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

`⦃ ⦄` is the Aeneas total-correctness triple. Under limb bounds on the inputs, the real
step returns a value with no panic, no overflow and no divergence. The reference step on
the mapped inputs also returns a value. The four output coordinates are equal under `toZ`,
and every output limb is below `2^52`. The output bound implies the input bounds, so the
invariant carries from one step to the next. The reference step does not read the `z`
coordinate of the base point, so `z1` is arbitrary.

The theorem is a corollary of `differential_add_and_double_refines` (`lean/Sim/Pilot.lean`),
which takes the four field contracts `C : FieldContracts` as a premise.
`field_contracts` (`lean/Sim/Discharge.lean`) proves the four contracts from the ported
`add_spec`, `sub_spec`, `mul_spec` and `square_spec`. `FieldContracts` is stated in
`Pilot.lean`, which does not import the spec files, and the kernel checks that the
statements agree.

## 4. Assumptions

Premises. They appear in the statement: every limb of the four point coordinates is below
`2^53`, and every limb of `u` is below `2^54`.

Trusted definitions. `#print axioms` does not show them.

1. The port to plain Rust computes the same as the hacspec spec. Its Rust tests pass
   RFC 7748 section 5.2 vector 1 and section 6.1, with hacspec's `nat_mod` field.
2. The Lean field model computes the same as hacspec's `nat_mod`. `field.Fe` is
   `ZMod (2^255 - 19)` (`lean/X25519Ref/TypesExternal.lean`). `fe_add`, `fe_sub`, `fe_mul`
   and `fe_sq` are the ring operations. `fe_inv` is the `ZMod` inverse, which maps 0 to 0
   as `nat_mod`'s `inv` does. `fe_from_bytes` decodes little-endian and reduces mod p.
   `fe_to_bytes` encodes the canonical representative. The ladder step uses only the ring
   operations and `fe_lit`.
3. The 6 hand definitions for `subtle` and `zeroize` on the real side. The step does not
   use them. `subtle.Choice.from` panics on inputs other than 0 and 1, where Rust has only
   a `debug_assert!`.
4. The real code is `lean-verify`'s modified copy of dalek. The theorem holds for that
   copy.

Axioms. `lake env lean Sim/AxiomsDischarge.lean` gives only `propext`, `Classical.choice`
and `Quot.sound` for the theorem, for `field_contracts` and for each contract.

## 5. Proof structure

`Pilot.lean` (204 lines) has three parts:

1. Lockstep. 19 `step with` calls, one per real field operation (18) and one for the
   constant `APLUS2_OVER_FOUR`. Each uses a contract restated over `toZ` (`add_z`,
   `sub_z`, `mul_z`, `square_z`).
2. Bounds. 21 goals of the form `exact bnd_mono h (by norm_num)`. The bounds were chosen
   by hand: 53 for `add`, 63 or 54 for `sub`, 54 for `mul` and `square`.
3. Representation. `point_add_and_double_eq` computes the reference step in closed form.
   Four ring identities in `ZMod p` close the output goals. One needs `AA = BB + E`, because
   dalek computes `z2` as `E * (121666 E + BB)` and RFC 7748 as `E * (AA + 121665 E)`.

The two control flows match call for call at the level of field operations. This does not
extend to the ladder. The reference runs 256 iterations, with a conditional swap before
and after each step. dalek runs 255 iterations with lazy swaps and a final swap. After the first
iteration, the two states agree only up to a common projective factor, so a ladder theorem
needs a hand-written invariant.

No proof sets `maxHeartbeats`. Two carry stages of `lean-verify` used about 335,000
heartbeats on our pin, above the default 200,000. They now step over three calls to
`carry_block`, with its own spec, and use about 55,000. The largest proof in the track,
`mul_product_stage_spec`, uses 151,845. Some proofs set `maxRecDepth 4096`.

## 6. Checks

1. `lake build` in `lean/` passes. No file in `lean/Sim/` or `lean/Curve25519Dalek/` has a
   `sorry`.
2. `lake env lean Sim/Axioms.lean` and `lake env lean Sim/AxiomsDischarge.lean` print the
   axiom lists of section 4.
3. `cargo test` in `ref-plain/` passes both RFC tests.
4. `lake env lean Sim/RefVectors.lean` runs the Lean reference, with the `ZMod` model, on
   the same two RFC vectors and prints `true` twice. This trusts the Lean compiler, and it
   is a test, not a proof.
5. `scripts/check-short-names.py` finds no name in `lean/X25519Ref` and
   `lean/Curve25519Dalek` that Lean binds to a different declaration from the crate-level
   one (Aeneas issue #1458).

## 7. Strengths and weaknesses

Strengths:

1. The step is the cleanest lockstep of the three tracks. The two sides match operation
   for operation.
2. No primitive is opaque. Both sides reduce to arithmetic mod p.
3. The premises are only limb bounds, and the axioms are only the standard three.
4. The relation is total, and the output bound carries to the next step.
5. The Lean reference reproduces two RFC test vectors.
6. The proved step and field code are the code that libsignal runs on 64-bit targets,
   apart from the extraction edits.

Weaknesses:

1. The unit is one step. The ladder needs a hand-written projective invariant.
2. The reference is a port, and the field model is hand-written. Their faithfulness rests
   on review and on two test vectors.
3. The real code is a modified copy of dalek. The theorem covers upstream dalek only if
   the 361-line diff preserves meaning.
4. The field proofs are ports of another project's proofs. Every Aeneas update can break
   them again, because they depend on the goal shapes after `step*`.

## 8. Reproduce

From the repository root, run `scripts/fetch-upstreams.sh` once. Then:

```bash
cd tracks/x25519/ref-plain && cargo test
cd ../lean && lake build
lake env lean Sim/Axioms.lean && lake env lean Sim/AxiomsDischarge.lean
lake env lean Sim/RefVectors.lean
for d in X25519Ref Curve25519Dalek; do ../../../scripts/check-short-names.py $(ls $d/*.lean | grep -v _Template); done
```

The extraction commands. Run them in `ref-plain/` and in `real-dalek/`, with the Aeneas
release of `.aeneas/` on `PATH`:

```bash
charon cargo --preset=aeneas --start-from crate::x25519_scalarmult --start-from crate::x25519_secret_to_public --start-from crate::point_add_and_double --opaque crate::field
aeneas -backend lean -split-files -loops-to-rec -namespace x25519_ref -dest Ref x25519_ref.llbc
```

```bash
charon cargo --preset=aeneas --start-from 'crate::montgomery::differential_add_and_double' --start-from 'crate::montgomery::MontgomeryPoint::mul_clamped' -- --locked -p curve25519-dalek --no-default-features --features alloc,zeroize
aeneas -backend lean -loops-to-rec -split-files -dest Mont curve25519_dalek.llbc
```

`lean/X25519Ref` and `lean/Curve25519Dalek` hold copies of `ref-plain/Ref` and
`real-dalek/Mont` with the hand edits of section 2.
