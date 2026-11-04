# Reference-to-real simulation through Aeneas

This repository tests one question. Take an RFC, a small Rust reference implementation of
it and a real Rust implementation. Aeneas translates both Rust programs to Lean. Can Lean
then prove that the real implementation computes what the reference computes? Four
studies, one per RFC, answer this. Each study ends in a Lean theorem with no `sorry`.
Tracks B (X25519) and D (Ristretto) prove full refinement for some public API pairs. Tracks
A (ChaCha20) and C (HPKE) prove one unit of their implementation each. Section 2 defines
these terms, and each track README gives the details.

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

## 2. The four studies

| Track | RFC | Reference | Real implementation | Result |
|---|---|---|---|---|
| [A](tracks/chacha20poly1305/README.md) | RFC 8439 (ChaCha20) | [hax-style ChaCha20 spec](https://github.com/cryspen/hax/tree/a1ddcfffd617a9f29442acb900a01df7339f3ea8/examples/chacha20) (`cryspen/hax`) | [libcrux HACL ChaCha20](https://github.com/cryspen/libcrux/tree/3ade18381ad3144d755507f97994933d8585839b/crates/algorithms/chacha20poly1305) (`cryspen/libcrux`) | unit: the block core |
| [B](tracks/x25519/README.md) | RFC 7748 (X25519) | [hacspec curve25519 spec](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/curve25519/src/curve25519.rs) (`hacspec/specs`), ported to plain Rust | [x25519-dalek 2.0.1](https://github.com/dalek-cryptography/curve25519-dalek/tree/4ac84dd0668b1d2e51654fcdffe4ae6a687bef00/x25519-dalek) on [curve25519-dalek 4.2.0](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek), as modified by `curve25519-dalek-lean-verify` | full refinement: `x25519` and `StaticSecret::diffie_hellman` |
| [C](tracks/hpke/README.md) | RFC 9180 (HPKE) | [hacspec HPKE spec](https://github.com/cryspen/hpke-spec/tree/85429a9ab519ca6eb5b286294203cefe75399223) (`cryspen/hpke-spec`) behind a library shim | [`cryspen/hpke-rs` 0.6.1](https://github.com/cryspen/hpke-rs/tree/e1a4b12d3e630c713a89e97a2a91e4a597f3fc82) | unit: the key schedule, base mode, HKDF-SHA256 |
| [D](tracks/ristretto/README.md) | RFC 9496 (ristretto255) | [hacspec ristretto spec](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/ristretto/src/ristretto.rs) (`hacspec/specs`), ported to plain Rust | [curve25519-dalek 4.2.0](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek), as modified by `curve25519-dalek-lean-verify` (the copy of track B) | full refinement: `decompress` and `compress` |

Each track README is self-contained. It gives the sources, the translation and its edits,
and the exact theorem. It also gives the assumptions, the proof structure, the checks, and
the strengths and weaknesses of the track.

Full refinement, in this repository, is a theorem that relates one public function of the
real implementation to one public function of the reference, on all inputs. This is an
API pair. Full refinement for one pair says nothing about the other public functions of
either program. The end goal is full refinement for every public function of the real
implementation that has a counterpart in the reference. Each study started from one unit
below one API pair, a small part that tests the method at a low cost. A full theorem needs
the unit theorem and one more result for each layer between the unit and the API. Section
1 of each track README shows this call path, the status of each layer and the results
that are still missing.

## 3. Method

Translation. Charon reads the MIR of each Rust program and writes LLBC. Aeneas reads LLBC
and writes Lean. Both programs of a track go into one Lake project, in separate
namespaces. All tracks use one tool version: Aeneas `nightly-2026.10.12-d119a47`, Charon
`0.1.281`, Rust `nightly-2026-09-17` and Lean `v4.31.0`. Each track records every source
edit and every hand-written Lean definition.

Relation. Each track defines its own relation between the two representations. Track A
compares 32-bit word lists. Tracks B and D map five 64-bit limbs in radix `2^51` to an
element of `ZMod (2^255 - 19)` and also bound the limbs. Track C compares byte strings and
maps algorithm identifiers.

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

## 4. Results

| Track | Main theorem | Premises | Axioms beyond the standard 3 |
|---|---|---|---|
| A | `Sim.core_refines` | output buffer size, equal states | none |
| B | `X25519Sim.x25519_refines`, `X25519Sim.static_diffie_hellman_as_bytes_refines` | none | none |
| C | `Sim.key_schedule_base_refines` | a model of the crypto provider, base mode, a bound on `info` | 4 formatting declarations, 24 `native_decide` auxiliary axioms |
| D | `RistrettoSim.decompress_refines`, `RistrettoSim.compress_refines` | for encoding, limbs below `2^53` | none |

All main theorems are proved. Every relation is total. Each theorem proves that both
programs succeed on the premise domain, with no panic or overflow, and that the results
agree. Sections 3 and 4 of each track README give the exact statement and the trusted
base.

## 5. Strengths

1. Real code goes through Aeneas with few edits. Tracks A and C need at most 1 line on the
   real side. Tracks B and D use a copy of dalek that another project made extractable.
2. The theorems are total-correctness statements about the translation of the real code.
3. Where the control flows line up, the proof is mechanical. One rule per matching step
   closes most of the proof.
4. The trusted base is explicit. Premises are in the statements, the axioms are listed and
   explained, and no proof raises the heartbeat limit.
5. The method finds real differences between the implementations, for example the HKDF
   salt of hpke-rs and the different `z2` formula of dalek.
6. libsignal ships code that the tracks prove: dalek's X25519 agreement (track B), the
   hpke-rs key schedule (track C), and dalek's Ristretto decoding and encoding (track D).
   libsignal uses later versions of dalek. A source comparison, not a proof, relates the
   proved code to those versions.

## 6. Weaknesses and limits

1. Old hacspec specifications do not go through Aeneas. Track A uses a hax-style spec,
   tracks B and D a port to plain Rust, and track C a library shim. The ports and the shim
   are trusted.
2. No reference is checked against its RFC by proof. Only tracks B and D run RFC test
   vectors. The reference of track D is modelled on dalek, so a shared error of the two
   programs is not found. The track B README lists the gaps between RFC 7748, the
   reference and x25519-dalek.
3. Full refinement covers only some API pairs, and only in tracks B and D. Tracks A and C
   prove one small unit each. Each track README lists what is not covered. Loops whose
   shapes differ between the two sides need hand-written invariants, for example the
   ladder of track B.
4. Opaque primitives limit what a theorem says. In track C, HMAC and SHA-2 are opaque, and
   the provider premises stay assumptions.
5. The proofs are manual. No generic lockstep tactic exists yet. Section 5 of each track
   README measures where one applies.
6. The proofs depend on one Aeneas version. Proofs from another Aeneas version need a
   port, as track B shows.

## 7. Repository layout

| Path | Content |
|---|---|
| `tracks/<track>/README.md` | the full description of the track |
| `tracks/<track>/lean/` | the Lake project: generated code, hand-written models, proofs in `Sim/` |
| `shared/dalek/` | the curve25519-dalek extraction and Lean library that tracks B and D import, with the field specs in `lean/Curve25519Dalek/Specs/` ([README](shared/dalek/README.md)) |
| `tracks/<track>/` other directories | work copies of the Rust sources and extraction scripts |
| `scripts/fetch-upstreams.sh` | clones the upstream repositories at the recorded commits and prepares the Lean projects |
| `scripts/check-short-names.py` | the name-binding scan that section 6 of each track README runs |
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
