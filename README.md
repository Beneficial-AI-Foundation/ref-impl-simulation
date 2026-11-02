# Reference-to-real simulation through Aeneas

This repository tests one question. Take an RFC, a small Rust reference implementation of
it and a real Rust implementation. Aeneas translates both Rust programs to Lean. Can Lean
then prove that the real implementation computes what the reference computes? Three
feasibility studies, one per RFC, answer this for one unit of each implementation. Each
study ends in a Lean theorem with no `sorry`. Track B also proves a theorem about the
whole X25519 function. Tracks A and C do not prove a theorem about their whole public API.
Section 2 shows where each unit sits in that larger goal.

## 1. Problem

A cryptographic RFC often comes with a reference implementation that reads like the
specification: small, direct and potentially with no focus on optimizations. The implementations that ship are different code:
optimized, unrolled, with other data representations. A proof that the real code
computes the same as the reference transfers trust from the readable code to the shipped
code.

Aeneas translates safe Rust into pure Lean functions in a `Result` monad, through Charon,
which reads the Rust compiler's MIR. If both programs go through Aeneas, the question
becomes a question about two Lean functions. This project asks three things:

1. Do both kinds of code go through Charon and Aeneas, and with how many edits?
2. Can Lean prove a refinement theorem between the two translations?
3. How much of that proof is generic, so that a tactic can produce it?

The target theorem relates a real function `real.f` and a reference function `ref.f`
through a relation `R_in` on inputs and `R_out` on outputs:

```lean
theorem real_refines_ref (x : RealIn) (y : RefIn) (h : R_in x y) :
    real.f x ⦃ r => ∃ s, ref.f y = .ok s ∧ R_out r s ⦄
```

`⦃ ⦄` is the total-correctness triple of the Aeneas library. If the statement holds, the
real function returns `ok r`, with no panic, no arithmetic overflow and no divergence.
The reference then also returns `ok s`, and `R_out r s` holds. Both
programs are deterministic, so the theorem states that the results agree on every input
that satisfies the premises.

## 2. The three studies

| Track | RFC | Reference | Real implementation | Unit |
|---|---|---|---|---|
| [A](tracks/chacha20poly1305/README.md) | RFC 8439 (ChaCha20) | [hax-style ChaCha20 spec](https://github.com/cryspen/hax/tree/a1ddcfffd617a9f29442acb900a01df7339f3ea8/examples/chacha20) (`cryspen/hax`) | [libcrux HACL ChaCha20](https://github.com/cryspen/libcrux/tree/3ade18381ad3144d755507f97994933d8585839b/crates/algorithms/chacha20poly1305) (`cryspen/libcrux`) | block core |
| [B](tracks/x25519/README.md) | RFC 7748 (X25519) | [hacspec curve25519 spec](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/curve25519/src/curve25519.rs) (`hacspec/specs`), ported to plain Rust | [curve25519-dalek 4.2.0](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek), as modified by `curve25519-dalek-lean-verify` | one Montgomery ladder step, then the full X25519 function |
| [C](tracks/hpke/README.md) | RFC 9180 (HPKE) | [hacspec HPKE spec](https://github.com/cryspen/hpke-spec/tree/85429a9ab519ca6eb5b286294203cefe75399223) (`cryspen/hpke-spec`) behind a library shim | [`cryspen/hpke-rs` 0.6.1](https://github.com/cryspen/hpke-rs/tree/e1a4b12d3e630c713a89e97a2a91e4a597f3fc82) | key schedule, base mode, HKDF-SHA256 |

Each track README is self-contained. It gives the sources, the translation and its edits,
and the exact theorem. It also gives the assumptions, the proof structure, the checks, and
the strengths and weaknesses of the track.

The unit is not the end goal. The end goal is full refinement: a theorem that relates the
public API of the real implementation to the public API of the reference. Each track
proves one unit inside that API. The unit is a small part of the API, so it tests the
method at a low cost. A full theorem needs the unit theorem and
one more result for each layer between the unit and the API. Section 1 of each track
README has the subsection "The unit in full refinement". It shows the call path from the
API down to the unit and the status of each layer. It also lists the missing results:

| Track | Public API pair | Main missing result |
|---|---|---|
| [A](tracks/chacha20poly1305/README.md#the-unit-in-full-refinement) | `chacha20_encrypt` against `chacha20`, then the AEAD | the key setup, the message loop, and a Poly1305 reference |
| [B](tracks/x25519/README.md#the-unit-in-full-refinement) | `mul_clamped` against `x25519_scalarmult` | none. `X25519Sim.mul_clamped_refines` is proved |
| [C](tracks/hpke/README.md#the-unit-in-full-refinement) | `Hpke::seal` and `open` against `HpkeSeal` and `HpkeOpen` | extraction of the reference API, the KEM, and the context as a forward simulation |

## 3. Method

Translation. Charon reads the MIR of each Rust program and writes LLBC. Aeneas reads LLBC
and writes Lean. Both programs of a track go into one Lake project, in separate
namespaces. All tracks use one tool version: Aeneas `nightly-2026.10.12-d119a47`, Charon
`0.1.281`, Rust `nightly-2026-09-17` and Lean `v4.31.0`. Each track records every source
edit and every hand-written Lean definition.

Relation. Each track defines its own relation between the two representations. Track A
compares 32-bit word lists. Track B maps five 64-bit limbs in radix `2^51` to an element
of `ZMod (2^255 - 19)` and also bounds the limbs. Track C compares byte strings and maps
algorithm identifiers.

Proof. The proofs use the Aeneas `step` tactics on each side. Where the two control flows
reach a matching point, a lockstep rule takes one step on each side and relates the
results. Such a point is a call, a field operation or a shared primitive. Where the flows
differ, the proof needs a hand-written lemma or invariant.

Trust accounting. Each track states its trusted base in four parts:

1. Premises. They appear in the theorem statement.
2. Trusted definitions. These are hand-written Lean models of functions that Aeneas leaves
   opaque, and Rust shims or ports. `#print axioms` does not show them.
3. Axioms. `#print axioms` lists them for every main theorem. Each track names every axiom
   outside `propext`, `Classical.choice` and `Quot.sound`.
4. Tools. rustc's MIR, Charon, Aeneas, the Aeneas Lean library and the Lean kernel.

Rules for the proofs. No `sorry`. No hand-written proof changes `maxHeartbeats`, so every
proof fits the default limit of 200,000 heartbeats. A proof that does not fit is split
into lemmas. The files that Aeneas generates set 1,000,000 for their own definitions.


| | A ChaCha20 | B X25519 | C HPKE |
|---|---|---|---|
| Main theorem | `Sim.core_refines` | `X25519Sim.differential_add_and_double_refines_proved` (the step) and `X25519Sim.mul_clamped_refines` (full refinement) | `Sim.key_schedule_base_refines` |
| Premises | output buffer of 16 words, `ctx` equals the reference state | limb bounds for the step. None for full refinement | the provider computes the shared HKDF model and the RFC lengths, and its PRNG call succeeds. Base mode with empty PSK, HKDF-SHA256, matching identifiers, a bound on the length of `info` |
| Trusted definitions | none | the plain-Rust port, the `ZMod p` field model, 6 `subtle` and `zeroize` models. Only full refinement uses the `subtle` and `zeroize` models | the shared HKDF model (HMAC opaque), the cryptolib model, the `hacspec_lib` shim, 6 `std` models |
| Axioms beyond the standard 3 | none | none | 4 formatting declarations, 24 `native_decide` auxiliary axioms |
| Source edits | reference 33 lines, real 0 lines | reference port 166 changed lines and a 32-line field module, real 0 lines here (361 lines in `curve25519-dalek-lean-verify`) | reference 0 lines (shim 179 lines), real 1 line |
| Lockstep | at the call level: 18 of 18 calls | at the level of field operations: 19 steps | only at the shared HKDF calls |

All main theorems are proved. Every relation is total. Each theorem proves that both
programs succeed on the premise domain, with no panic or overflow, and that the results
agree.

## 5. Strengths

1. Real code goes through Aeneas with few edits. Track A needs 0 lines on the real side
   and track C needs 1 line. Track B uses a copy of dalek that another project changed in
   361 lines to make it extractable.
2. The theorems are total-correctness statements about the translation of the real code.
   Track B proves the modified copy of dalek. In track C, the real side runs on models of
   6 `std` functions and on an abstract provider.
3. Where the control flows line up, the proof is mechanical. In tracks A and B, one rule
   per matching step closes most of the proof.
4. The trusted base is explicit. Premises are in the statements, the axioms are listed and
   explained, and no proof raises the heartbeat limit.
5. The method finds real differences between the implementations. Examples are the HKDF
   salt of hpke-rs, its short-PSK check and the different `z2` formula of dalek.
6. Two of the three real units are code that libsignal ships: the dalek ladder step and
   field code (track B) and the hpke-rs key schedule (track C).

## 6. Weaknesses and limits

1. Old hacspec specifications do not go through Aeneas. Track A uses a
   hax-style spec, track B a port to plain Rust, and track C a library shim. The port and
   the shim are trusted.
2. No reference is checked against its RFC by proof. Only track B runs RFC test vectors,
   and only two.
3. Only track B proves full refinement, and only for `mul_clamped`. Tracks A and C prove
   one small unit each: a block core and one key schedule mode. Section 2 lists what they
   still need. Loops whose shapes differ between the two sides need hand-written
   invariants. Track B shows the cost: its ladder needed a scaling argument, because after
   the first iteration the two states agree only up to a projective factor.
4. Opaque primitives limit what a theorem says. In track C, HMAC and SHA-2 are opaque,
   and the provider premises stay assumptions because the RustCrypto provider does not
   extract.
5. The proofs are manual. No generic lockstep tactic exists yet. Sections 5 of the track
   READMEs measure where one applies.
6. The proofs depend on one Aeneas version. Proofs from another Aeneas version need a
   port, as track B shows.

## 7. Repository layout

| Path | Content |
|---|---|
| `tracks/<track>/README.md` | the full description of the track |
| `tracks/<track>/lean/` | the Lake project: generated code, hand-written models, proofs in `Sim/` (track B also in `Curve25519Dalek/Specs/`) |
| `tracks/<track>/` other directories | work copies of the Rust sources and extraction scripts |
| `scripts/fetch-upstreams.sh` | clones the upstream repositories at the recorded commits and prepares the Lean projects |
| `scripts/check-short-names.py` | the name-binding scan of section 3 |
| `NOTICE.md` | the third-party code in this repository and its licenses |

## 8. Reproduce

1. Unpack the Aeneas release `nightly-2026.10.12-d119a47` into `.aeneas/` at the
   repository root. It contains `aeneas`, `charon`, `charon-driver` and
   `backends/lean`. Install the Rust toolchain named in `.aeneas/rust-toolchain`.
2. Run `scripts/fetch-upstreams.sh` from the repository root.
3. In each `tracks/<track>/lean/`, run `lake build`. The first build fetches Mathlib and
   the other Lean packages.
4. Follow section 8 of each track README for the extraction and the axiom checks.

## 9. License

The code and documentation of this repository are under the MIT license (`LICENSE`). The
third-party work copies keep their own licenses, which `NOTICE.md` lists.
