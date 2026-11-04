//! Differential tests of the port's `point_mul` against the unchanged hacspec edwards25519
//! `point_mul`, the unchanged hacspec Ristretto `mul` and curve25519-dalek 5.0.0.
mod vectors;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar as DalekScalar;
use hacspec_edwards25519 as he;
use hacspec_lib::*;
use hacspec_ristretto as hr;
use ristretto_ref::edwards::{point_identity, point_mul, EdPoint};
use ristretto_ref::field::{fe_from_bytes, fe_lit, fe_mul, fe_to_bytes};
use ristretto_ref::scalar::{sc_bit, sc_from_bytes};
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

/// l, little-endian.
fn l_bytes() -> [u8; 32] {
    hex::<32>("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010")
}

/// 2 l, little-endian. 2 l is below 2^254, so it fits in 32 bytes.
fn two_l_bytes() -> [u8; 32] {
    let l = l_bytes();
    let mut r = [0u8; 32];
    let mut carry = 0u8;
    for i in 0..32 {
        r[i] = (l[i] << 1) | carry;
        carry = l[i] >> 7;
    }
    r
}

/// 53 scalars: 0, 1, 2, 3, l - 1, l - 2, l, l + 1, 2 l, 2^252, 2^252 - 1, 2^255, 2^256 - 1, and
/// 40 random 32-byte strings. The random strings use all 256 bits, so most of them are reduced
/// mod l.
fn scalars() -> Vec<[u8; 32]> {
    let l = l_bytes();
    let mut l1 = l; l1[0] -= 1;
    let mut l2 = l; l2[0] -= 2;
    let mut lp1 = l; lp1[0] += 1;
    let mut t = [0u8; 32]; t[31] = 0x10;
    let mut t1 = [0xffu8; 32]; t1[31] = 0x0f;
    let mut h = [0u8; 32]; h[31] = 0x80;
    let mut v = vec![
        le(&[0]), le(&[1]), le(&[2]), le(&[3]), l1, l2, l, lp1, two_l_bytes(), t, t1, h,
        [0xffu8; 32],
    ];
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

/// The order-2 point `(0, -1, 1, 0)`. `-1` is `p - 1`, little-endian.
fn order_two() -> Coords {
    let mut m1 = [0xffu8; 32]; m1[0] = 0xec; m1[31] = 0x7f;
    [[0u8; 32], m1, le(&[1]), [0u8; 32]]
}

/// `(λX, λY, λZ, λT)` with `λ = 7`: the same affine point with `Z ≠ 1`.
fn rescale(c: Coords) -> Coords {
    let lam = fe_lit(7);
    let f = |b: [u8; 32]| fe_to_bytes(fe_mul(fe_from_bytes(b), lam));
    [f(c[0]), f(c[1]), f(c[2]), f(c[3])]
}

/// On the decoded RFC points, the port gives the same four coordinates as the unchanged
/// edwards25519 spec, and `encode` of the port gives the bytes of the unchanged Ristretto `mul`
/// and of dalek 5.0.0 (12 points, 53 scalars).
#[test]
fn point_mul_matches_specs_and_dalek() {
    for b in points() {
        let c = port_coords(decode(b).ok().expect("an RFC multiple decodes"));
        for k in scalars() {
            let port = port_mul(k, c);
            assert_eq!(port, spec_ed_mul(k, c), "edwards25519 spec, k = {:02x?}, P = {:02x?}", k, b);
            let enc = port_encode(port);
            assert_eq!(enc, spec_ristretto_mul(k, b), "Ristretto spec, k = {:02x?}, P = {:02x?}", k, b);
            assert_eq!(enc, dalek_mul(k, b), "dalek, k = {:02x?}, P = {:02x?}", k, b);
        }
    }
}

/// `a` and `b` have `Z ≠ 0` and stand for the same affine point: `X_a Z_b = X_b Z_a` and
/// `Y_a Z_b = Y_b Z_a`.
fn same_affine(a: Coords, b: Coords) -> bool {
    let f = fe_from_bytes;
    let mul = |x: [u8; 32], y: [u8; 32]| fe_to_bytes(fe_mul(f(x), f(y)));
    a[2] != [0u8; 32] && b[2] != [0u8; 32]
        && mul(a[0], b[2]) == mul(b[0], a[2]) && mul(a[1], b[2]) == mul(b[1], a[2])
}

/// The identity `(0, 1, 1, 0)`.
fn identity() -> Coords {
    [[0u8; 32], le(&[1]), le(&[1]), [0u8; 32]]
}

/// The theorem covers every represented point, not only the decoded ones. On a rescaled
/// input and on the order-2 point, the port gives the same four coordinates as the unchanged
/// edwards25519 spec.
#[test]
fn point_mul_matches_edwards_spec_off_ristretto() {
    let mut inputs: Vec<Coords> = points().into_iter().take(3)
        .map(|b| rescale(port_coords(decode(b).ok().unwrap()))).collect();
    inputs.push(order_two());
    for c in inputs {
        for k in scalars() {
            assert_eq!(port_mul(k, c), spec_ed_mul(k, c), "k = {:02x?}, P = {:02x?}", k, c);
        }
    }
}

/// Checks that do not use hacspec as the oracle. A rescaled input gives the same affine
/// result as the original input. On the order-2 point `T`, the port computes
/// `(k mod l) • T`: `l` and `2 l` give the identity, `1` and `l + 1` give `T`, and `2` gives
/// the identity. `T` is not the identity, so `l • T = T` differs from `(l mod l) • T`.
#[test]
fn point_mul_affine_properties() {
    for b in points().into_iter().take(3) {
        let c = port_coords(decode(b).ok().unwrap());
        for k in scalars() {
            assert!(same_affine(port_mul(k, c), port_mul(k, rescale(c))), "k = {:02x?}, P = {:02x?}", k, b);
        }
    }
    let t = order_two();
    let l = l_bytes();
    let mut lp1 = l; lp1[0] += 1;
    assert!(!same_affine(t, identity()));
    assert!(same_affine(port_mul(le(&[1]), t), t));
    assert!(same_affine(port_mul(le(&[2]), t), identity()));
    assert!(same_affine(port_mul(l, t), identity()));
    assert!(same_affine(port_mul(two_l_bytes(), t), identity()));
    assert!(same_affine(port_mul(lp1, t), t));
}

/// The reason for the edwards25519 reference: the Ristretto `mul` of 2 and the identity
/// returns `(0, 0, 0, 0)`, which is not a valid representative. The port keeps `Z ≠ 0`.
#[test]
fn ristretto_mul_degenerates_on_identity() {
    let two = hr::Scalar::from_byte_seq_le(Seq::<U8>::from_public_slice(&le(&[2])));
    let (x, y, z, t) = hr::mul(two, hr::IDENTITY_POINT());
    let zero = hr::FieldElement::ZERO();
    assert!(x == zero && y == zero && z == zero && t == zero);
    let (_, _, z, _) = point_mul(sc_from_bytes(le(&[2])), point_identity());
    assert_ne!(fe_to_bytes(z), [0u8; 32]);
}

/// `sc_bit` reads the bits of the reduced value: `l - 1` gives its own bits, `l` gives 0.
#[test]
fn sc_bit_reads_reduced_value() {
    let l = l_bytes();
    let mut l1 = l; l1[0] -= 1;
    for i in 0..256 {
        assert_eq!(sc_bit(sc_from_bytes(l1), i), (l1[i / 8] >> (i % 8)) & 1 == 1, "bit {}", i);
        assert!(!sc_bit(sc_from_bytes(l), i), "bit {}", i);
    }
}

/// hacspec `bit` panics for an index of 256 or more, as the Lean model `scalar.sc_bit` fails.
#[test]
#[should_panic]
fn sc_bit_panics_at_256() {
    sc_bit(sc_from_bytes(le(&[1])), 256);
}
