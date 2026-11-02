# Track C: HPKE key schedule (RFC 9180)

All paths are relative to `tracks/hpke/`.

## 1. Unit and sources

| Role | Code | Commit |
|---|---|---|
| Reference | [`cryspen/hpke-spec`](https://github.com/cryspen/hpke-spec/tree/85429a9ab519ca6eb5b286294203cefe75399223), old hacspec | `85429a9a` (2022-09-15) |
| Reference library | [`hacspec/hacspec` `lib/`](https://github.com/hacspec/hacspec/tree/4ecc847fc944fe996e19423aa41f002f2039dab0/lib) | `4ecc847f` |
| Real | [`cryspen/hpke-rs` 0.6.1](https://github.com/cryspen/hpke-rs/tree/e1a4b12d3e630c713a89e97a2a91e4a597f3fc82) | `e1a4b12d` (2026-07-16) |

The unit is the key schedule of RFC 9180 section 5.1 in base mode: `KeySchedule`,
`LabeledExtract` and `LabeledExpand`. The theorems cover the key schedule only. The next
subsection shows where it sits in the full HPKE API.

hpke-spec has no license, so this repository does not include it. `make-ref-shim.sh`
builds the work tree `ref-shim/` from a clone and `patches/hpke-spec.patch`.

### The unit in full refinement

Full refinement for HPKE is a theorem about the public API. For single-shot encryption,
it relates the real `Hpke::seal` and `Hpke::open` to the reference `HpkeSeal` and
`HpkeOpen`. The table follows the call path from this pair down to the unit. A full proof
relates each pair of functions in the table.

| Layer | Reference (`lean/Ref`) | Real (`lean/Real`) | Status |
|---|---|---|---|
| Single-shot API | `HpkeSeal`, `HpkeOpen` | `Hpke::seal`, `Hpke::open` | real side extracted only |
| Setup, base mode | `SetupBaseS`, `SetupBaseR` | `Hpke::setup_sender`, `Hpke::setup_receiver` | real side extracted only |
| KEM | `Encap`, `Decap` | `kem::encaps`, `kem::decaps` | real side extracted only |
| Key schedule (the unit) | `KeySchedule` | `Hpke::key_schedule` | proved for base mode and HKDF-SHA256 |
| Labeled KDF | `LabeledExtract`, `LabeledExpand` | `kdf::labeled_extract`, `kdf::labeled_expand` | proved |
| Context | `ContextS_Seal`, `ContextR_Open`, `Context_Export` | `Context::seal`, `Context::open`, `Context::export` | real side extracted only |
| Secret export | `SendExport`, `ReceiveExport` | `Hpke::send_export`, `Hpke::receiver_export` | real side extracted only |

The reference extraction starts from `KeySchedule` (`ref-extract.sh`), so the reference
functions above it are not in Lean. The real extraction covers the whole public surface
(section 2).

Full refinement of base-mode HPKE needs five more results:

1. Extraction of the reference API. The reference extraction must start from the
   functions above `KeySchedule`. This project did not try it.
2. The KEM. On the reference side, the Diffie-Hellman functions of the crypto library are
   opaque. On the real side, they are methods of the provider. A shared model of X25519,
   with premises on the provider, can play the same role as the shared HKDF model. DHKEM
   derives the shared secret with `LabeledExtract` and `LabeledExpand`, so the KDF
   theorems apply there.
3. The context. `seal`, `open` and `export` change the sequence number, so they need a
   forward simulation: a relation between the two contexts that holds at the start and
   that every call keeps. `KsRel`, the relation of the key schedule theorem, gives the
   start.
4. The AEAD. It is opaque on both sides, like HMAC. The theorem can use a shared AEAD
   model, with premises on the provider, as it does for HKDF.
5. Composition. The theorems for `seal` and `open` chain the results of all layers.

The other modes need more. The key schedule theorem covers base mode with an empty PSK
only. The PSK, Auth and AuthPSK modes need the same chain, with their own setup functions
and the PSK premises. For the KDFs HKDF-SHA384 and HKDF-SHA512 the reference fails
(section 4), so no theorem can relate the two sides there.

## 2. Translation

Both programs go through Charon and Aeneas into one Lake project (`lean/`), in the
namespaces `Ref` and `Real`.

Reference. Aeneas fails on the original `hacspec_lib`, because of the supertraits of
`SeqTrait` (Aeneas issue #1164). A plain-Rust shim with the same names replaces it
(`shim/hacspec-lib`, 119 lines). A second shim gives the signatures of the crypto library
(`shim/hacspec_cryptolib`, 60 lines). Charon treats its 8 functions as opaque. The spec
source files are unchanged. The patch changes the manifests and the root toolchain file,
removes the 5 per-crate toolchain files and adds a lockfile.
`ref-extract.sh` runs the extraction, starting from `KeySchedule`.

Real. hpke-rs is generic over the trait `HpkeCrypto`, which supplies the primitives. Aeneas
turns the trait into a structure, so every function takes an instance as a parameter. One
source line changed: `label: &'static str` became `label: &str` (`real-work/src/kdf.rs`).
`util::xor_bytes` is opaque. `real-extract.sh` extracts the whole public surface. The
RustCrypto provider does not extract (Charon issue #1519, then Aeneas issue #1112).

Hand-written Lean. `lean/patch-externals.py` turns the generated templates into the
`FunsExternal.lean` files. On the reference side, it defines `hkdf_extract` and
`hkdf_expand` from the shared model (section 4). On the real side, it replaces 6 of the 50
function axioms with models of `std` functions. 44 function axioms remain. Section 4 lists
the ones that the theorem uses. One `sed` line in `ref-extract.sh` removes a `discriminant` attribute that clashes
with an instance name on the real side. No reference code reads that discriminant. The
script also copies `Real/TypesExternal_Template.lean` to `Real/TypesExternal.lean`, which
keeps 2 type axioms (`core.fmt.builders.DebugStruct`, `subtle.Choice`).

## 3. Statement

`lean/Sim/Rel.lean` defines a relational triple over two Aeneas programs:

```lean
def rel (m₁ : Result α) (m₂ : Result β) (R : α → β → Prop) : Prop :=
  m₁ ⦃ a => m₂ ⦃ b => R a b ⦄ ⦄
```

`⦃ ⦄` is the Aeneas total-correctness triple. If `rel m₁ m₂ R` holds, the real program
`m₁` returns `ok a`, the reference `m₂` returns `ok b`, and `R a b` holds. A panic, an overflow
or divergence on either side makes it false.

The main theorem is `Sim.key_schedule_base_refines` (`lean/Sim/KeySchedule.lean`):

```lean
theorem key_schedule_base_refines (inst : HpkeCrypto C P E1 E2)
    (self : Real.Hpke C P E1 E2) (hm : self.mode = .Base)
    (hX : ExtractIsShared inst self.kdf_id) (hE : ExpandIsShared inst self.kdf_id)
    (hL : LengthsStd inst) (hP : ∃ p, inst.prng = ok p)
    (k d a) (hS : d = .HKDF_SHA256)
    (hk : KemRel k self.kem_id) (hd : KdfIdRel d self.kdf_id) (ha : AeadRel a self.aead_id)
    (ss info psk psk_id rss rinfo rpsk rpsk_id)
    (h1 : rss.b.val = ss.val) (h2 : rinfo.b.val = info.val)
    (hpsk : psk.val = []) (hpsk_id : psk_id.val = [])
    (hrpsk : rpsk.b.val = []) (hrpsk_id : rpsk_id.b.val = [])
    (hinfo : 200 + info.val.length ≤ Usize.max) :
    rel (Real.Hpke.key_schedule inst self ss info psk psk_id)
        (Ref.KeySchedule (.mode_base, k, d, a) rss rinfo rpsk rpsk_id) KsRel
```

`KsRel r s` states that both sides return `Ok` and that the two contexts have equal key,
base nonce, sequence number and exporter secret. The relation does not compare the `Hpke`
value with a fresh PRNG that the real context also carries.

Three lemma-level theorems in `lean/Sim/Kdf.lean` have the same form:
`labeled_extract_refines`, `labeled_extract_refines_zero_salt` (real salt `[0x00]` against
reference salt empty) and `labeled_expand_refines`. Their relation `OkRel` states that both
sides return `Ok` with equal bytes.

`lean/Sim/Witness.lean` shows that the premises can hold together. It defines a provider
`inst` that computes HKDF with the shared model and fails on every other operation. It
then applies the theorem to the suite DHKEM(X25519, HKDF-SHA256), HKDF-SHA256,
AES-128-GCM, with empty shared secret, `info`, PSK and PSK identifier
(`Sim.Witness.key_schedule_instance`).

## 4. Assumptions

Premises. They appear in the statement.

1. `ExtractIsShared inst alg`: for the KDF of the suite, the provider's `kdf_extract`
   returns the shared model's HKDF-Extract.
2. `ExpandIsShared inst alg`: for the KDF of the suite and a PRK of hash length, the
   provider's `kdf_expand` returns the shared model's HKDF-Expand. If the model fails, the
   provider returns some error. RFC 5869 requires a PRK of at least the hash length, and
   the key schedule passes exactly that length.
3. `LengthsStd inst`: the provider's `Nk`, `Nn` and `Nh` are the RFC 9180 values.
4. The provider's PRNG call succeeds.
5. The KDF is HKDF-SHA256 (`hS`). The original hacspec cryptolib supports only SHA-256 for
   HKDF. For SHA-384 and SHA-512 the reference fails, and the theorem does not apply.
6. Base mode, with an empty PSK and PSK identifier on both sides.
7. `200 + |info| ≤ Usize.max`, so that no concatenation overflows.
8. The inputs correspond: equal shared secret and `info` bytes, and matching KEM, KDF and
   AEAD identifiers.

No extracted provider discharges premises 1 to 4, because the RustCrypto provider does not
extract. The witness of section 3 is a model, not a real provider. For an extracted
provider, premise 3 also needs models of the three trait default methods, which are
axioms in the generated Lean today.

Trusted definitions. `#print axioms` does not show them.

9. The shared HKDF model (`lean/Shared/Hkdf.lean`). `hmacBlock` (HMAC on a normalized key)
   and `longKey` (the hashed form of a key longer than the block) are opaque. The RFC 2104
   key padding (`normKey`), HKDF-Extract and HKDF-Expand (RFC 5869) are defined from them.
   Both sides use this one model. The theorem says nothing about HMAC or SHA-2.
10. The reference model of the crypto library (`lean/Ref/FunsExternal.lean`). It defines
    `hkdf_extract` and `hkdf_expand` from the shared model for SHA-256. For SHA-384 and
    SHA-512 it returns `UNSUPPORTED_ALGORITHM`, as the original cryptolib does.
11. The `hacspec_lib` shim computes the same as the original library. Nothing checks this.
    The spec's known-answer tests do not compile against the shim, so the shimmed reference
    never ran the RFC test vectors.
12. The models of 6 `std` functions on the real side: `Borrow::borrow`, `str::as_bytes`,
    `<[T]>::join` and its `Join` impl, `hint::must_use` and `fmt::format`. `format` is
    modeled as total and returns the opaque string `Real.fmtString`. If a `Display` impl
    fails, Rust's `format!` panics. The helper `Real.vecOfList` builds a `Vec` and panics
    if the length exceeds `Usize.max`.
13. The hacspec spec is a correct reading of RFC 9180. This project does not check it.

Axioms. `lake env lean Sim/Axioms.lean` gives, for `key_schedule_base_refines`:

- `propext`, `Classical.choice`, `Quot.sound`.
- 4 formatting axioms. `Aeneas.Std.core.fmt.Formatter` comes from the Aeneas library.
  `Str.Insts.CoreFmtDisplay.fmt`, `hpke_rs_crypto.error.Error.Insts.CoreFmtDisplay.fmt` and
  `alloc.string.ToString.Blanket.to_string` come from the real extraction
  (`lean/Real/FunsExternal.lean`). They occur only on error paths. Each is a type or a
  function into an inhabited type, so they are consistent.
- 24 `native_decide` auxiliary axioms. 11 come from `toStr` in the generated `Real` code.
  13 come from the proofs: the 6 label lemmas `Sim.str_*` give 12, and the theorem itself
  gives 1. They trust the Lean compiler as well as the kernel. The kernel cannot evaluate
  `String.toByteArray`, so `decide` does not replace them.

The three KDF theorems depend on the three standard axioms and on the library axiom
`Aeneas.Std.core.fmt.Formatter`.

## 5. Proof structure

The proof uses three rules: `rel_bind_left` takes a step on the real side, `rel_bind_right`
on the reference side, and `rel_bind` a matched pair of steps. The two control flows do not
match call for call, so `rel_bind` is never used. hpke-rs groups calls into helper
functions, maps errors after each primitive call and joins several slices in one
`concat`. The reference uses label functions and binary `concat`. The two sides meet only
at the calls of the shared HKDF functions.

Five representation gaps need a lemma or a relation:

1. HKDF salt. hpke-rs passes `[0x00]`, and RFC 9180 and the reference pass the empty
   string. The two give the same PRK because HMAC pads short keys with zeros
   (`Shared.extract_salt_zero`).
2. Big-endian encoding: `to_be_bytes` against shifts.
3. Identifiers: lookup tables against enum casts.
4. Lengths: values from the provider against constants.
5. Byte strings: `Seq U8` against `Vec U8`.

Each HKDF-Expand in the key schedule requests at most 255 times the hash length, so the
model cannot fail there (`Shared.expand_ne_none`). This is why `KsRel` has no error case.

The proof also found two differences between hpke-rs and the reference outside the
premises. In the PSK modes, hpke-rs rejects a PSK shorter than 32 bytes and the reference
accepts it. For `LabeledExpand`, the reference rejects `L > 255 * Nh`, but hpke-rs checks
only `L > 65535` and leaves the rest to the provider.

## 6. Checks

1. `lake build` in `lean/` passes. No file in `lean/Sim/` or `lean/Shared/` has a `sorry`
   or sets `maxHeartbeats`.
2. `lake env lean Sim/Axioms.lean` prints the axiom lists of section 4.
3. Running `make-ref-shim.sh`, `ref-extract.sh`, `real-extract.sh` and
   `patch-externals.py` again gives files in `lean/Ref` and `lean/Real` that are identical
   to the committed ones (2026-11-02).
4. `scripts/check-short-names.py` finds no name in `lean/Ref` and `lean/Real` that Lean
   binds to a different declaration from the crate-level one
   (Aeneas issue #1458). The script reads text and does not elaborate.

## 7. Strengths and weaknesses

Strengths:

1. The proof is about the shipped code. hpke-rs changed by one line, and the spec source
   files did not change.
2. The theorem holds for every provider that satisfies the premises, because hpke-rs is
   generic. The premises are stated so that a real provider can meet them: they cover only
   the suite's KDF, only PRKs of hash length, and any error value.
3. The relation is total. Both sides succeed on the whole premise domain.
4. The HKDF model is concrete except for HMAC, so the theorem covers the HKDF structure.

Weaknesses:

1. The unit is one function in base mode with one KDF.
2. The reference is a 2022 hacspec spec behind a hand-written shim, and that combination
   never ran the RFC test vectors.
3. HMAC and SHA-2 are opaque. The provider premises stay assumptions until a provider
   extracts.
4. 24 `native_decide` axioms widen the trusted base to the Lean compiler.
5. The proof is manual. Each side needs closed forms of its small functions, and no
   lockstep tactic exists yet.

## 8. Reproduce

From the repository root, run `scripts/fetch-upstreams.sh` once. Then, in `tracks/hpke/`:

```bash
./ref-extract.sh && ./real-extract.sh
cd lean && python3 patch-externals.py && lake build
lake env lean Sim/Axioms.lean
for d in Ref Real; do ../../../scripts/check-short-names.py $(ls $d/*.lean | grep -v _Template); done
```

The extraction scripts overwrite `lean/Ref` and `lean/Real`. The committed files are their
output.
