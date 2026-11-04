//! Scalars mod l = 2^252 + 27742317777372353535851937790883648493. Opaque to Charon
//! (`--opaque crate::scalar`). Executable semantics come from hacspec_lib's nat_mod, with the
//! same definition as `Scalar` in hacspec/specs edwards25519/src/edwards25519.rs. The Lean
//! model is ZMod l, written by hand in TypesExternal.lean and FunsExternal.lean.
use hacspec_lib::*;

public_nat_mod!(
    type_name: ScalarElement,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

#[derive(Clone, Copy)]
pub struct Scalar(ScalarElement);

/// hacspec: `Scalar::from_byte_seq_le(b)`. Little-endian, all 256 bits, mod l.
pub fn sc_from_bytes(b: [u8; 32]) -> Scalar {
    Scalar(ScalarElement::from_byte_seq_le(Seq::<U8>::from_public_slice(&b)))
}
/// hacspec: `s.bit(i)`. Bit `i` of the canonical representative, below l.
pub fn sc_bit(s: Scalar, i: usize) -> bool { s.0.bit(i) }
