import ForkRistretto.Dalek

/-! # Axiom checks of the Ristretto theorems

This file is apart from `Checks/Axioms.lean`, because the reference libraries `X25519Ref` and
`RistrettoRef` both declare the root namespace `field`, so no module imports both.

The reference theorems use only the three standard axioms. The dalek theorems add the fork's
models of two Rust crates, each one axiom that states that the crate's functions meet their
contracts:

- `RustAx.core`: `core` (`Curve25519Dalek/FunsExternal.lean` in the fork).
- `RustAx.subtle`: `subtle` (`Subtle/Contract.lean` in the fork).

The fork's `decompress` and `compress` specs of the two i686 builds do not use `RustAx.core`. -/

/-- info: 'ForkRistretto.decode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.decode_spec

/-- info: 'ForkRistretto.encode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.encode_spec

/-- info: 'ForkRistretto.ref_sqrt_ratio_m1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.ref_sqrt_ratio_m1

/-- info: 'ForkRistretto.point_mul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.point_mul_spec

/-- info: 'ForkRistretto.point_mul_spec_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.point_mul_spec_of

/-- info: 'ForkRistretto.point_mul_encode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.point_mul_encode_spec

/-- info: 'ForkRistretto.addExt_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkRistretto.addExt_rep

/--
info: 'ForkRistretto.«x86_64-tables».decompress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-tables».decompress_refines

/--
info: 'ForkRistretto.«x86_64-tables».compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-tables».compress_refines

/--
info: 'ForkRistretto.«x86_64-tables».mul_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-tables».mul_refines

/--
info: 'ForkRistretto.«x86_64-tables».mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-tables».mul_compress_refines

/--
info: 'ForkRistretto.«x86_64-tables».decompress_mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-tables».decompress_mul_compress_refines

/--
info: 'ForkRistretto.«i686-tables».decompress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-tables».decompress_refines

/-- info: 'ForkRistretto.«i686-tables».compress_refines' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs in #print axioms ForkRistretto.«i686-tables».compress_refines

/--
info: 'ForkRistretto.«i686-tables».mul_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-tables».mul_refines

/--
info: 'ForkRistretto.«i686-tables».mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-tables».mul_compress_refines

/--
info: 'ForkRistretto.«i686-tables».decompress_mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-tables».decompress_mul_compress_refines

/--
info: 'ForkRistretto.«x86_64-no-tables».decompress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-no-tables».decompress_refines

/--
info: 'ForkRistretto.«x86_64-no-tables».compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-no-tables».compress_refines

/--
info: 'ForkRistretto.«x86_64-no-tables».mul_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-no-tables».mul_refines

/--
info: 'ForkRistretto.«x86_64-no-tables».mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-no-tables».mul_compress_refines

/--
info: 'ForkRistretto.«x86_64-no-tables».decompress_mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«x86_64-no-tables».decompress_mul_compress_refines

/--
info: 'ForkRistretto.«i686-no-tables».decompress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-no-tables».decompress_refines

/--
info: 'ForkRistretto.«i686-no-tables».compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-no-tables».compress_refines

/--
info: 'ForkRistretto.«i686-no-tables».mul_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-no-tables».mul_refines

/--
info: 'ForkRistretto.«i686-no-tables».mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-no-tables».mul_compress_refines

/--
info: 'ForkRistretto.«i686-no-tables».decompress_mul_compress_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkRistretto.«i686-no-tables».decompress_mul_compress_refines
