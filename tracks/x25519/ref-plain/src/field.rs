//! Field GF(2^255-19). Opaque to Charon (`--opaque crate::field`).
//! Executable semantics come from hacspec_lib's nat_mod. The Lean model
//! is ZMod p, written by hand in FunsExternal.lean / TypesExternal.lean.
use hacspec_lib::*;

public_nat_mod!(
    type_name: X25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

#[derive(Clone, Copy)]
pub struct Fe(X25519FieldElement);

pub fn fe_lit(x: u32) -> Fe { Fe(X25519FieldElement::from_literal(x as u128)) }
pub fn fe_add(a: Fe, b: Fe) -> Fe { Fe(a.0 + b.0) }
pub fn fe_sub(a: Fe, b: Fe) -> Fe { Fe(a.0 - b.0) }
pub fn fe_mul(a: Fe, b: Fe) -> Fe { Fe(a.0 * b.0) }
pub fn fe_sq(a: Fe) -> Fe { Fe(a.0.pow(2u128)) }
pub fn fe_inv(a: Fe) -> Fe { Fe(a.0.inv()) }
/// Little-endian decode, reduced mod p.
pub fn fe_from_bytes(b: [u8; 32]) -> Fe {
    Fe(X25519FieldElement::from_byte_seq_le(Seq::<U8>::from_public_slice(&b)))
}
/// Canonical little-endian encoding.
pub fn fe_to_bytes(a: Fe) -> [u8; 32] {
    let s = a.0.to_byte_seq_le();
    let mut out = [0u8; 32];
    for i in 0..32 { out[i] = s[i].declassify(); }
    out
}
