# Reference-to-real simulation through Aeneas

This repository tests one question. Take an RFC, a small Rust reference implementation of
it and a real Rust implementation. Aeneas translates both Rust programs to Lean. Can Lean
then prove that the real implementation computes what the reference computes? Four
studies, one per RFC, answer this. Each study ends in a Lean theorem with no `sorry`.
Track B proves full refinement for five functions of x25519-dalek. `x25519` and the
`diffie_hellman` method of the three secret types, one of which libsignal calls, each agree
with the reference `x25519_scalarmult` on every input. `x25519` on the constant
`X25519_BASEPOINT_BYTES` agrees with `x25519_secret_to_public`.
`SharedSecret::was_contributory` after `diffie_hellman` agrees with a check for the
all-zero shared secret that we added to the reference. The accessors are proved to be the
identity. Key generation, public-key derivation, the conversions and the trait impls of
x25519-dalek are not covered. Track D proves full refinement for two API pairs of Ristretto:
decoding on every input, and encoding on every input whose limbs are below `2^53`. Tracks
A and C prove one unit of their implementation each. Section 2 shows where each unit sits
in the larger goal.

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

| Track | RFC | Reference | Real implementation | Unit |
|---|---|---|---|---|
| [A](tracks/chacha20poly1305/README.md) | RFC 8439 (ChaCha20) | [hax-style ChaCha20 spec](https://github.com/cryspen/hax/tree/a1ddcfffd617a9f29442acb900a01df7339f3ea8/examples/chacha20) (`cryspen/hax`) | [libcrux HACL ChaCha20](https://github.com/cryspen/libcrux/tree/3ade18381ad3144d755507f97994933d8585839b/crates/algorithms/chacha20poly1305) (`cryspen/libcrux`) | block core |
| [B](tracks/x25519/README.md) | RFC 7748 (X25519) | [hacspec curve25519 spec](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/curve25519/src/curve25519.rs) (`hacspec/specs`), ported to plain Rust | [x25519-dalek 2.0.1](https://github.com/dalek-cryptography/curve25519-dalek/tree/4ac84dd0668b1d2e51654fcdffe4ae6a687bef00/x25519-dalek) on [curve25519-dalek 4.2.0](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek), as modified by `curve25519-dalek-lean-verify` | `x25519` and the three `diffie_hellman` methods against `x25519_scalarmult`, `x25519` on `X25519_BASEPOINT_BYTES` against `x25519_secret_to_public`, and `was_contributory` against our all-zero check (full refinement for these pairs). The accessors are proved to be the identity |
| [C](tracks/hpke/README.md) | RFC 9180 (HPKE) | [hacspec HPKE spec](https://github.com/cryspen/hpke-spec/tree/85429a9ab519ca6eb5b286294203cefe75399223) (`cryspen/hpke-spec`) behind a library shim | [`cryspen/hpke-rs` 0.6.1](https://github.com/cryspen/hpke-rs/tree/e1a4b12d3e630c713a89e97a2a91e4a597f3fc82) | key schedule, base mode, HKDF-SHA256 |
| [D](tracks/ristretto/README.md) | RFC 9496 (ristretto255) | [hacspec ristretto spec](https://github.com/hacspec/specs/blob/c511110d6f4bb4628da193a2c8e44c928d9555b8/ristretto/src/ristretto.rs) (`hacspec/specs`), ported to plain Rust | [curve25519-dalek 4.2.0](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/26d49052347e52cb3923952ea225d28faf48fe72/curve25519-dalek), as modified by `curve25519-dalek-lean-verify` (the copy of track B) | `CompressedRistretto::decompress` against `decode`, and `RistrettoPoint::compress` against `encode` (full refinement for these pairs) |

Each track README is self-contained. It gives the sources, the translation and its edits,
and the exact theorem. It also gives the assumptions, the proof structure, the checks, and
the strengths and weaknesses of the track.

Full refinement, in this repository, is a theorem that relates one public function of the
real implementation to one public function of the reference, on all inputs. This is an
API pair. Full refinement for one pair says nothing about the other public functions of
either program. The end goal is full refinement for every public function of the real
implementation that has a counterpart in the reference. Each study started from one unit
below one API pair, a small part that tests the method at a low cost. A full theorem needs
the unit theorem and one more result for each layer between the unit and the API. Tracks
B and D have all these results for their pairs. Section 1 of each track README shows the
call path from the API down to the unit and the status of each layer. For tracks A and C,
it also lists the missing results:

| Track | Public API pair | Main missing result |
|---|---|---|
| [A](tracks/chacha20poly1305/README.md#the-unit-in-full-refinement) | `chacha20_encrypt` against `chacha20`, then the AEAD | the key setup, the message loop, and a Poly1305 reference |
| [B](tracks/x25519/README.md#layers-of-the-full-refinement) | `x25519_dalek::x25519` and the three `diffie_hellman` methods against `x25519_scalarmult`, and `was_contributory` against our all-zero check | none for these pairs. `X25519Sim.x25519_refines`, `X25519Sim.static_diffie_hellman_as_bytes_refines` and the theorems for the other secret types and for `was_contributory` are proved. The two `From<[u8; 32]>` impls that libsignal uses, at key construction and in the agreement, are linked by review, not by proof. The other public functions are not covered ([list](tracks/x25519/README.md#gaps-rfc-7748-the-reference-and-x25519-dalek)) |
| [C](tracks/hpke/README.md#the-unit-in-full-refinement) | `Hpke::seal` and `open` against `HpkeSeal` and `HpkeOpen` | extraction of the reference API, the KEM, and the context as a forward simulation |
| [D](tracks/ristretto/README.md#3-statement) | `decompress` against `decode`, `compress` against `encode` | none for these pairs. `RistrettoSim.decompress_refines` and `RistrettoSim.compress_refines` are proved. For scalar multiplication, only the reference side is proved (`RistrettoSim.point_mul_spec`). The real side, the other group operations and `from_uniform_bytes` are not covered |

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

The shared library `shared/dalek/` adds a fifth part:

5. Edits of the generated Lean. The two patches in `shared/dalek/patches/` each change one
   call, so that Lean elaborates it. `shared/dalek/inline-table.py` replaces the 768 binds of
   the basepoint table with one literal. Lean does not check these edits against the Aeneas
   output. The theorems that use `Curve25519Dalek/Funs.lean` hold for the edited text.

Rules for the proofs. No `sorry`. No hand-written proof changes `maxHeartbeats`, so every
proof fits the default limit of 200,000 heartbeats. A proof that does not fit is split
into lemmas. The files that Aeneas generates set 1,000,000 for their own definitions.

## 4. Results

| | A ChaCha20 | B X25519 | C HPKE | D Ristretto |
|---|---|---|---|---|
| Main theorem | `Sim.core_refines` | `X25519Sim.x25519_refines`, `X25519Sim.static_diffie_hellman_as_bytes_refines` and `X25519Sim.static_diffie_hellman_was_contributory_refines` (full refinement for the API pairs of the track README), with `X25519Sim.mul_clamped_refines` and the ladder step `X25519Sim.differential_add_and_double_refines_proved` as layers | `Sim.key_schedule_base_refines` | `RistrettoSim.decompress_refines` and `RistrettoSim.compress_refines` (full refinement for two API pairs) |
| Premises | output buffer of 16 words, `ctx` equals the reference state | none | the provider computes the shared HKDF model and the RFC lengths, and its PRNG call succeeds. Base mode with empty PSK, HKDF-SHA256, matching identifiers, a bound on the length of `info` | none for decoding. For encoding, every limb of the point is below `2^53` |
| Trusted definitions | none | the plain-Rust port, the `ZMod p` field model, 10 `subtle` and `zeroize` models, 4 of them only for `was_contributory`. For libsignal's use, the review of two `From<[u8; 32]>` impls | the shared HKDF model (HMAC opaque), the cryptolib model, the `hacspec_lib` shim, 6 `std` models | the plain-Rust port, the `ZMod p` field model, 7 `subtle` models and the type `Choice` from the shared library |
| Axioms beyond the standard 3 | none | none | 4 formatting declarations, 24 `native_decide` auxiliary axioms | none |
| Source edits | reference 33 lines, real 0 lines | reference port 229 changed lines (166 for the port, 63 for our 9-line all-zero check and the new tests) and a 32-line field module, real 0 lines here (361 lines in `curve25519-dalek-lean-verify`, 0 in x25519-dalek) | reference 0 lines (shim 179 lines), real 1 line | reference port of 172 lines with a 50-line field module, real 0 lines here (the copy of track B) |
| Lockstep | at the call level: 18 of 18 calls | in the ladder step, at the level of field operations: 19 steps. The ladder needs a hand-written invariant | only at the shared HKDF calls | at the level of field operations, in `sqrt_ratio_i`, `decompress` and `compress`. The rejection tests need two hand-written arguments |

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
6. libsignal ships code that the tracks prove: dalek's X25519 agreement path from
   `StaticSecret::diffie_hellman` down (track B), the hpke-rs key schedule (track C), and
   dalek's Ristretto decoding and encoding (track D). libsignal uses later versions of
   dalek. For tracks B and D, a source comparison, not a proof, relates the proved code
   to those versions.

## 6. Weaknesses and limits

1. Old hacspec specifications do not go through Aeneas. Track A uses a
   hax-style spec, tracks B and D a port to plain Rust, and track C a library shim. The
   ports and the shim are trusted.
2. No reference is checked against its RFC by proof. Only tracks B and D run RFC test
   vectors. Track B runs the RFC 7748 vectors of sections 5.2 and 6.1, with the iterated
   test up to 1,000 iterations, and a set of edge inputs. Track D runs the 45
   cases of RFC 9496, Appendix A.1 and A.2, and the 6 cases of A.4. The reference of
   track D is modelled on dalek, so a shared error of the two programs is not found.
   Track B's reference also misses two
   parts of RFC 7748: key generation and the check for the all-zero shared secret. Track B
   adds the check to the reference, so the check rests on review and tests. The
   track B README lists the gaps between the RFC, the reference and x25519-dalek.
3. Only tracks B and D prove full refinement, and only for some API pairs. Track B covers
   x25519-dalek's `x25519`, the three `diffie_hellman` methods, the accessors,
   `X25519_BASEPOINT_BYTES` and `was_contributory`. libsignal also uses the two
   `From<[u8; 32]>` impls, at key construction and in the agreement. They are not
   extracted, and only review links them to the theorems. Track B does not cover key
   generation, `PublicKey::from(&secret)`, which derives the public key through Edwards
   tables, or the trait impls. Track D covers Ristretto decoding and encoding, but
   not the group operations. Tracks A and C prove one small
   unit each: a block core and one key schedule mode. Section 2 lists what they
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
| `tracks/<track>/lean/` | the Lake project: generated code, hand-written models, proofs in `Sim/` |
| `shared/dalek/` | the curve25519-dalek extraction and Lean library that tracks B and D import, with the field specs in `lean/Curve25519Dalek/Specs/` ([README](shared/dalek/README.md)). It also extracts the basepoint table path of the X25519 public key and proves that entry `j` of row `i` of the table encodes `[(j + 1) 256^i] B` mod `p`, with every limb below `2^52` |
| `tools/` | scripts that compute certificates and witness points for the proofs in `shared/dalek/lean/DalekSim/`. The proofs check them, so the scripts are not trusted |
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
