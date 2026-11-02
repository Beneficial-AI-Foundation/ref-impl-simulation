# Track A: ChaCha20 block core (RFC 8439)

All paths are relative to `tracks/chacha20poly1305/`.

## 1. Unit and sources

| Role | Code | Commit |
|---|---|---|
| Reference (used) | [`cryspen/hax` `examples/chacha20`](https://github.com/cryspen/hax/tree/a1ddcfffd617a9f29442acb900a01df7339f3ea8/examples/chacha20), hax style | `a1ddcfff` |
| Reference (tried) | old hacspec [ChaCha20](https://github.com/hacspec/hacspec/tree/4ecc847fc944fe996e19423aa41f002f2039dab0/examples/chacha20) and [Poly1305](https://github.com/hacspec/hacspec/tree/4ecc847fc944fe996e19423aa41f002f2039dab0/examples/poly1305), `hacspec/hacspec` | `4ecc847f` |
| Real | libcrux HACL ChaCha20-Poly1305, [`crates/algorithms/chacha20poly1305`](https://github.com/cryspen/libcrux/tree/3ade18381ad3144d755507f97994933d8585839b/crates/algorithms/chacha20poly1305) | `3ade1838` |

The unit is the ChaCha20 block core of RFC 8439: the quarter round, the double round, the
20 rounds, and the core that adds the input state. Key setup (`chacha20_init`), the byte
encoding, encryption over a message, Poly1305 and the AEAD are out of scope.

libsignal does not use libcrux HACL ChaCha20-Poly1305. On 2026-10-30, it used RustCrypto
`chacha20poly1305`, only for the Noise channel to Signal's enclave services. This track
tests the method on code that Signal does not ship.

## 2. Translation

Both programs go through Charon and Aeneas into one Lake project (`lean/`), in the
namespaces `Ref` and `Real`.

Reference. The old hacspec spec fails in Aeneas on the supertraits of `SeqTrait` (Aeneas
issue #1164). A 1-line edit gets the core through, but the byte layer and Poly1305 still
fail (`ref-hacspec/`). The track uses the hax-style port of the same spec instead
(`ref-hax/`). It has plain Rust arrays and `wrapping_add`. Its dependency
`hax-bounded-integers` does not build, so one `sed` command changes 33 lines: an index type
alias and 32 calls of `.into_checked()`. The extraction has 0 errors and 0 axioms.
`Ref/Funs.lean` has 498 lines and covers the whole ChaCha20 spec.

Real. HACL ChaCha20 extracts with no source edit. The build glue is a root `Cargo.toml` and
5 manifest lines. `Real/Funs.lean` has 1826 lines and no axioms. The Aeneas library lacks
`U32::wrapping_div` and `wrapping_rem`, so `Real/FunsExternal.lean` and
`RealAead/FunsExternal.lean` each define them. In `Real`, only `chacha20_update` uses
`wrapping_rem`, outside the theorems. In `RealAead`, Poly1305 also uses both.

HACL Poly1305 and the AEAD also extract (`RealAead/Funs.lean`, 3085 lines), after a
rewrite of 52 lines of `mac_poly1305.rs`. The rewrite was scripted. The script is not kept,
but the edited file is in `real/poly1305/`. Aeneas fails on a copy of a `&mut` borrow
inside a tuple (Aeneas issue #1461). The rewrite replaces each such tuple binding with a
destructuring. No theorem uses `RealAead`.

| Edit | Size |
|---|---|
| Reference source (hax style) | 33 lines, one `sed` command |
| HACL ChaCha20 source | 0 lines |
| HACL Poly1305 source | 52 lines |
| Build glue | a root `Cargo.toml`, 5 manifest lines and a `rust-toolchain` |
| Lean side | 2 definitions (`wrapping_div`, `wrapping_rem`) in each of `Real` and `RealAead` |

## 3. Statement

Each theorem has this shape (`lean/Sim/`):

```lean
real ⦃ r => ∃ s, ref = .ok s ∧ r.val = s.val ⦄
```

`⦃ ⦄` is the Aeneas total-correctness triple. The real program returns `ok r` with no
panic, no overflow and no divergence. The reference returns `ok s`, and the two values
have equal lists of 32-bit words. The real state is a `Slice U32` with `u32` indices. The
reference state is a 16-word `Array U32` with `usize` indices. The input relation is equal
word lists and equal index values.

| Theorem | File | Premises | Status |
|---|---|---|---|
| `quarter_round_refines` | `Sim/QuarterRound.lean` | indices below 16, `a ≠ d`, `c ≠ b` | proved |
| `double_round_refines` | `Sim/QuarterRound.lean` | none beyond the input relation | proved |
| `rounds_refines` | `Sim/Rounds.lean` | none beyond the input relation | proved |
| `core_refines` | `Sim/Core.lean` | output buffer of length 16, `ctx` equal to the reference state | proved |
| `core_refines_encrypt_block` | `Sim/Core.lean` | `ctx` equal to the reference state | proved |

The main theorem:

```lean
theorem core_refines (k ctx : Slice Std.U32) (st0 : Std.Array Std.U32 16#usize)
    (ctr : Std.U32) (hk : k.length = 16) (hc : ctx.val = st0.val) :
    Real.hacl.chacha20.chacha20_core k ctx ctr
      ⦃ r => ∃ s, Ref.chacha20_core ctr st0 = .ok s ∧ r.val = s.val ⦄
```

HACL's `chacha20_core` also works for buffers longer than 16 words. The theorem covers
length 16 exactly, which is the length at its call site. `core_refines_encrypt_block`
instantiates it at that call site in `chacha20_encrypt_block`, where the buffer is a fresh
16-word array, so only the premise on `ctx` remains. No theorem relates the `ctx` that
`chacha20_init` builds to the reference state.

Three helper theorems support `core_refines`:

- `add_state_loop_spec`: the invariant of the reference `add_state` loop.
- `Real.core_split`: the HACL core equals a prefix followed by `coreTail`, by `rfl`.
- `coreTail_spec`: the tail adds `ctx` to each word and the counter to word 12.

## 4. Assumptions

Premises. They appear in the statements.

1. Quarter round: all four indices are below 16, `a ≠ d` and `c ≠ b`. The 8 call sites in
   the double round use distinct literal indices. `decide` discharges the premises there.
2. Block core: the output buffer has 16 words, and `ctx` holds the same words as the
   reference state.

Trusted definitions. The theorems use none. Both extractions bottom out in the Aeneas
library: `u32` wrapping arithmetic, shifts, and index and update on arrays and slices. The
two hand-written definitions are used only outside the theorems.

Other trust points:

3. The 33-line edit of the hax spec does not change its meaning. It replaces a bounded
   index type with `usize` and removes 32 bound checks. Nothing checks this.
4. The hax spec is a correct reading of RFC 8439. This project does not check it.

Axioms. `lake env lean Sim/Axioms.lean` gives only `propext`, `Classical.choice` and
`Quot.sound` for every theorem. No proof uses `native_decide` or `bv_decide`.

## 5. Proof structure

One generic rule, `lockstep_bind` (`Sim/Basic.lean`), takes one bind on each side and links
the results by a relation. At the call level the two sides match exactly. The double round
is 8 quarter-round calls on both sides, and the rounds are 10 double-round calls. Two
macros, `qr_bind` and `dr_bind`, close all 18 call steps.

Below the call level, the proof is not lockstep:

1. Quarter round. HACL reads three words and then writes twice. The reference writes
   `state[a]` and then reads `state[d]` again. If `a ≠ d` and `c ≠ b`, the two agree.
   HACL writes rotation as two shifts and an or, and the reference calls `rotate_left`.
   One bit-vector lemma relates them.
2. Loops. The reference loops over the rounds and over `add_state`, and HACL unrolls both
   loops. The rounds loop needs two `i32` range lemmas that the Aeneas library lacks and an
   unrolling lemma. The `add_state` loop needs an invariant.
3. Core. HACL adds the counter to word 12 twice, once before the rounds and once after the
   final additions. The reference adds it once, to the input state. Word 12 needs
   associativity and commutativity of `wrapping_add`.

The HACL tail after the rounds has 16 unrolled blocks `k[i] = k[i] + ctx[i]`, each through
`split_at_mut(k, 0)`. `step*` over the whole tail exceeds the default 200,000 heartbeats.
`Sim/CoreTail.lean` rewrites the tail as 16 calls of one block function and proves the
block against an invariant once. Each application is then a separate step. No proof sets
`maxHeartbeats`. `Sim/Core.lean` and `Sim/CoreTail.lean` set `maxRecDepth 8192`, because
the unrolled terms are deep.

## 6. Checks

1. `lake build` in `lean/` passes. `lake build RealAead` also passes. No file in
   `lean/Sim/` has a `sorry`.
2. `lake env lean Sim/Axioms.lean` prints the axiom lists of section 4.
3. Running the commands of section 8 again gives `Funs.lean` and `Types.lean` files in
   `Ref/`, `Real/` and `RealAead/` that are identical to the committed ones (2026-11-02).
4. `scripts/check-short-names.py` finds no name in `lean/Ref`, `lean/Real` and
   `lean/RealAead` that Lean binds to a different declaration from the crate-level one
   (Aeneas issue #1458).

## 7. Strengths and weaknesses

Strengths:

1. The block core is proved end to end, with no premise beyond the call site's data.
2. The trusted base is the smallest of the three tracks. Both sides are extracted, no
   primitive is opaque, and the theorems use only the three standard axioms.
3. The real code is unchanged, and the reference needs only a mechanical edit.
4. The call level is fully lockstep. One rule and two macros close all 18 call steps.
5. The relation is total. Both sides succeed, with no panic or overflow.

Weaknesses:

1. The unit is the block core only. Key setup, the byte layer, encryption over a message,
   Poly1305 and the AEAD are not covered.
2. HACL's unrolled code is expensive for `step*`. The core tail needs its own
   decomposition.
3. Loops against unrolled code need a hand-written lemma per loop.
4. Inside the quarter round, the proof needs an aliasing premise and per-line glue.
5. Poly1305 has no reference that Aeneas accepts. The AEAD needs a hand-written reference
   and a relation between HACL's 26-bit limbs and the field modulo `2^130 - 5`.
6. Signal does not ship this code.

## 8. Reproduce

From the repository root, run `scripts/fetch-upstreams.sh` once. `run.sh <tag> <crate-dir>
<llbc-name> [charon args]` runs Charon on one crate and writes the LLBC file to
`out/<tag>/`. It also runs Aeneas into `out/<tag>-lean/` and reports errors and axioms. In `tracks/chacha20poly1305/`:

```bash
./run.sh refhax1 ref-hax chacha20_hax --start-from-pub
./run.sh realc real/chacha20poly1305 libcrux_chacha20poly1305 --start-from 'libcrux_chacha20poly1305::hacl::chacha20' --include 'libcrux_hacl_rs::*' --include 'libcrux_secrets::*'
./run.sh real5 real/chacha20poly1305 libcrux_chacha20poly1305 --start-from 'libcrux_chacha20poly1305::hacl' --include 'libcrux_hacl_rs::*' --include 'libcrux_poly1305::*' --include 'libcrux_secrets::*'
```

Aeneas then writes the Lean files into the project. Each command overwrites one
directory, but not the hand-written `FunsExternal.lean`:

```bash
A=../../.aeneas/aeneas; F="-backend lean -split-files -loops-to-rec -no-progress-bar -dest lean"
$A $F -subdir Ref -namespace Ref out/refhax1/chacha20_hax.llbc
$A $F -subdir Real -namespace Real out/realc/libcrux_chacha20poly1305.llbc
$A $F -subdir RealAead -namespace RealAead out/real5/libcrux_chacha20poly1305.llbc
```

Build and check:

```bash
cd lean && lake build && lake build RealAead
lake env lean Sim/Axioms.lean
for d in Ref Real RealAead; do ../../../scripts/check-short-names.py $d/*.lean; done
```
