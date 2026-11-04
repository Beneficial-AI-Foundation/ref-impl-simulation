//! Differential tests of the port's `point_mul` against the unchanged hacspec edwards25519
//! `point_mul`, the unchanged hacspec Ristretto `mul` and curve25519-dalek 5.0.0.
mod vectors;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar as DalekScalar;
use hacspec_edwards25519 as he;
use hacspec_lib::*;
use hacspec_ristretto as hr;
use ristretto_ref::edwards::{point_mul, EdPoint};
use ristretto_ref::field::{fe_from_bytes, fe_to_bytes};
use ristretto_ref::scalar::sc_from_bytes;
use ristretto_ref::{decode, encode};

type Coords = [[u8; 32]; 4];

fn port_coords(p: EdPoint) -> Coords {
    [fe_to_bytes(p.0), fe_to_bytes(p.1), fe_to_bytes(p.2), fe_to_bytes(p.3)]
}

fn ed_fe(b: [u8; 32]) -> he::Ed25519FieldElement {
    he::Ed25519FieldElement::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
}

fn ed_bytes(x: he::Ed25519FieldElement) -> [u8; 32] {
    let s = x.to_byte_seq_le();
    let mut r = [0u8; 32];
    for i in 0..32 { r[i] = s[i].declassify(); }
    r
}

/// The unchanged edwards25519 `point_mul`, on the scalar `Scalar::from_byte_seq_le(k)`.
fn spec_ed_mul(k: [u8; 32], c: Coords) -> Coords {
    let s = he::Scalar::from_byte_seq_le(Seq::<U8>::from_public_slice(&k));
    let (x, y, z, t) = he::point_mul(s, (ed_fe(c[0]), ed_fe(c[1]), ed_fe(c[2]), ed_fe(c[3])));
    [ed_bytes(x), ed_bytes(y), ed_bytes(z), ed_bytes(t)]
}

/// The port's `point_mul`, on the scalar `sc_from_bytes(k)`.
fn port_mul(k: [u8; 32], c: Coords) -> Coords {
    let p = (fe_from_bytes(c[0]), fe_from_bytes(c[1]), fe_from_bytes(c[2]), fe_from_bytes(c[3]));
    port_coords(point_mul(sc_from_bytes(k), p))
}

fn port_encode(c: Coords) -> [u8; 32] {
    encode((fe_from_bytes(c[0]), fe_from_bytes(c[1]), fe_from_bytes(c[2]), fe_from_bytes(c[3])))
}

/// The unchanged Ristretto spec: `encode(mul(k, decode(b)))`.
fn spec_ristretto_mul(k: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let p = hr::decode(hr::RistrettoPointEncoded::from_public_slice(&b)).unwrap();
    let s = hr::Scalar::from_byte_seq_le(Seq::<U8>::from_public_slice(&k));
    let out = hr::encode(hr::mul(s, p));
    let mut r = [0u8; 32];
    for i in 0..32 { r[i] = out[i].declassify(); }
    r
}

/// dalek 5.0.0: `(k mod l) * decompress(b)`, compressed.
fn dalek_mul(k: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let p = CompressedRistretto(b).decompress().unwrap();
    (DalekScalar::from_bytes_mod_order(k) * p).compress().to_bytes()
}

fn le(n: &[u8]) -> [u8; 32] {
    let mut r = [0u8; 32];
    r[..n.len()].copy_from_slice(n);
    r
}

/// 48 scalars: 0, 1, 2, 3, l - 1, l - 2, 2^252, 2^252 - 1, and 40 random 32-byte strings.
/// The random strings use all 256 bits, so most of them are reduced mod l.
fn scalars() -> Vec<[u8; 32]> {
    let l = hex::<32>("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");
    let mut l1 = l; l1[0] -= 1;
    let mut l2 = l; l2[0] -= 2;
    let mut t = [0u8; 32]; t[31] = 0x10;
    let mut t1 = [0xffu8; 32]; t1[31] = 0x0f;
    let mut v = vec![le(&[0]), le(&[1]), le(&[2]), le(&[3]), l1, l2, t, t1];
    let mut x: u64 = 0x6a09_e667_f3bc_c908;
    for _ in 0..40 {
        let mut b = [0u8; 32];
        for c in b.chunks_mut(8) {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            c.copy_from_slice(&x.to_le_bytes());
        }
        v.push(b);
    }
    v
}

fn hex<const N: usize>(s: &str) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N { r[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap(); }
    r
}

/// 12 encodings: the identity, the base point and 10 other RFC 9496 multiples of it.
fn points() -> Vec<[u8; 32]> {
    vectors::MULTIPLES.iter().take(12).copied().collect()
}

/// The port and the unchanged edwards25519 spec give the same four coordinates.
#[test]
fn point_mul_matches_edwards_spec() {
    for b in points() {
        let p = decode(b).ok().expect("an RFC multiple decodes");
        let c = port_coords(p);
        for k in scalars() {
            assert_eq!(port_mul(k, c), spec_ed_mul(k, c), "k = {:02x?}, P = {:02x?}", k, b);
        }
    }
}

/// `encode` of the port's `point_mul` gives the bytes of the hacspec Ristretto `mul` and of
/// dalek 5.0.0, on 12 points and 48 scalars (576 cases).
#[test]
fn point_mul_encodes_as_ristretto_mul() {
    for b in points() {
        let c = port_coords(decode(b).ok().unwrap());
        for k in scalars() {
            let port = port_encode(port_mul(k, c));
            assert_eq!(port, spec_ristretto_mul(k, b), "Ristretto spec, k = {:02x?}, P = {:02x?}", k, b);
            assert_eq!(port, dalek_mul(k, b), "dalek, k = {:02x?}, P = {:02x?}", k, b);
        }
    }
}
