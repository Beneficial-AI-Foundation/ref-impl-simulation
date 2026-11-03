//! Field GF(2^255-19). Opaque to Charon (`--opaque crate::field`).
//! Executable semantics come from hacspec_lib's nat_mod, with the same definition as
//! `FieldElement` in hacspec/specs ristretto/src/ristretto.rs. The Lean model is ZMod p,
//! written by hand in TypesExternal.lean and FunsExternal.lean.
use hacspec_lib::*;

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

#[derive(Clone, Copy)]
pub struct Fe(FieldElement);

/// hacspec: `fe(x)`, that is `FieldElement::from_literal(x as u128)`.
pub fn fe_lit(x: u32) -> Fe { Fe(FieldElement::from_literal(x as u128)) }
pub fn fe_add(a: Fe, b: Fe) -> Fe { Fe(a.0 + b.0) }
pub fn fe_sub(a: Fe, b: Fe) -> Fe { Fe(a.0 - b.0) }
pub fn fe_mul(a: Fe, b: Fe) -> Fe { Fe(a.0 * b.0) }
/// hacspec: `a.pow(2u128)`.
pub fn fe_sq(a: Fe) -> Fe { Fe(a.0.pow(2u128)) }
/// hacspec: `u == v`.
pub fn fe_eq(a: Fe, b: Fe) -> bool { a.0 == b.0 }
/// hacspec `is_negative`: `e % fe(2) == fe(1)`.
pub fn fe_is_negative(a: Fe) -> bool {
    a.0 % FieldElement::from_literal(2u128) == FieldElement::from_literal(1u128)
}
/// hacspec `sqrt_ratio_m1`: `x.pow_felem((P() - fe(5)) / fe(8))`.
pub fn fe_pow_p58(a: Fe) -> Fe {
    let p = FieldElement::from_byte_seq_be(&byte_seq!(
        0x7fu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xedu8
    ));
    let e = (p - FieldElement::from_literal(5u128)) / FieldElement::from_literal(8u128);
    Fe(a.0.pow_felem(e))
}
/// hacspec: `FieldElement::from_byte_seq_le(u)`. Little-endian, all 256 bits, mod p.
pub fn fe_from_bytes(b: [u8; 32]) -> Fe {
    Fe(FieldElement::from_byte_seq_le(Seq::<U8>::from_public_slice(&b)))
}
/// hacspec: `s.to_byte_seq_le()` written into 32 bytes. Canonical little-endian.
pub fn fe_to_bytes(a: Fe) -> [u8; 32] {
    let s = a.0.to_byte_seq_le();
    let mut out = [0u8; 32];
    for i in 0..32 { out[i] = s[i].declassify(); }
    out
}
