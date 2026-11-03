//! RFC 9496 test vectors and differential tests against the unchanged hacspec spec and
//! curve25519-dalek 5.0.0. The port is compared with the spec on the decoded coordinates,
//! the error code and `encode` of any tuple. dalek is compared on the round trip only,
//! because its point representation is private.
mod vectors;
use curve25519_dalek::ristretto::CompressedRistretto;
use hacspec_lib::*;
use hacspec_ristretto as h;
use ristretto_ref::field::{fe_from_bytes, fe_mul, fe_to_bytes, Fe};
use ristretto_ref::{decode, encode, sqrt_ratio_m1, DECODING_ERROR};

/// The four coordinates of a point as canonical little-endian bytes.
type Coords = [[u8; 32]; 4];

fn spec_fe_bytes(x: h::FieldElement) -> [u8; 32] {
    let s = x.to_byte_seq_le();
    let mut r = [0u8; 32];
    for i in 0..32 { r[i] = s[i].declassify(); }
    r
}

fn spec_fe(b: [u8; 32]) -> h::FieldElement {
    h::FieldElement::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
}

/// The unchanged spec's `decode`: the coordinates, or the error code.
fn spec_decode(b: [u8; 32]) -> Result<Coords, u8> {
    h::decode(h::RistrettoPointEncoded::from_public_slice(&b))
        .map(|(x, y, z, t)| [spec_fe_bytes(x), spec_fe_bytes(y), spec_fe_bytes(z), spec_fe_bytes(t)])
}

/// The port's `decode`: the coordinates, or the error code.
fn port_decode(b: [u8; 32]) -> Result<Coords, u8> {
    decode(b).map(|(x, y, z, t)| [fe_to_bytes(x), fe_to_bytes(y), fe_to_bytes(z), fe_to_bytes(t)])
}

/// The unchanged spec's `encode` on four coordinates.
fn spec_encode(c: Coords) -> [u8; 32] {
    let out = h::encode((spec_fe(c[0]), spec_fe(c[1]), spec_fe(c[2]), spec_fe(c[3])));
    let mut r = [0u8; 32];
    for i in 0..32 { r[i] = out[i].declassify(); }
    r
}

/// The port's `encode` on four coordinates.
fn port_encode(c: Coords) -> [u8; 32] {
    encode((fe_from_bytes(c[0]), fe_from_bytes(c[1]), fe_from_bytes(c[2]), fe_from_bytes(c[3])))
}

/// Compares `encode` of the port and of the spec on `c`.
fn check_encode(c: Coords) {
    assert_eq!(port_encode(c), spec_encode(c), "port and spec encode differ on {:02x?}", c);
}

/// Multiplies each coordinate by `l`, with the port's field operations.
fn scale(c: Coords, l: [u8; 32]) -> Coords {
    let l: Fe = fe_from_bytes(l);
    c.map(|x| fe_to_bytes(fe_mul(fe_from_bytes(x), l)))
}

/// The unchanged spec: `Some(encode(decode(b)))` or `None`.
fn spec_roundtrip(b: [u8; 32]) -> Option<[u8; 32]> {
    let e = h::RistrettoPointEncoded::from_public_slice(&b);
    match h::decode(e) {
        Ok(p) => {
            let out = h::encode(p);
            let mut r = [0u8; 32];
            for i in 0..32 { r[i] = out[i].declassify(); }
            Some(r)
        }
        Err(_) => None,
    }
}

fn port_roundtrip(b: [u8; 32]) -> Option<[u8; 32]> {
    match decode(b) {
        Ok(p) => Some(encode(p)),
        Err(e) => { assert_eq!(e, DECODING_ERROR); None }
    }
}

fn dalek_roundtrip(b: [u8; 32]) -> Option<[u8; 32]> {
    CompressedRistretto(b).decompress().map(|p| p.compress().to_bytes())
}

/// Compares the port with the spec (coordinates or error code, and the round trip) and with
/// dalek (the round trip). Returns the round trip of the port.
fn check_all(b: [u8; 32]) -> Option<[u8; 32]> {
    assert_eq!(port_decode(b), spec_decode(b), "port and spec decode differ on {:02x?}", b);
    let port = port_roundtrip(b);
    assert_eq!(port, spec_roundtrip(b), "port and spec differ on {:02x?}", b);
    assert_eq!(port, dalek_roundtrip(b), "port and dalek differ on {:02x?}", b);
    port
}

#[test]
fn rfc9496_multiples_of_generator() {
    for (i, b) in vectors::MULTIPLES.iter().enumerate() {
        assert_eq!(check_all(*b), Some(*b), "B[{i}]");
    }
}

#[test]
fn rfc9496_invalid_encodings() {
    for (group, b) in vectors::INVALID.iter() {
        assert_eq!(check_all(*b), None, "{group} {:02x?}", b);
    }
}

/// Edge inputs: s in 0..20, p - 1, p, p + 1, values with the top bit set, all bytes 0xff.
#[test]
fn edge_inputs() {
    let p_minus = |k: u8| {
        let mut b = [0xffu8; 32];
        b[0] = 0xed - k;
        b[31] = 0x7f;
        b
    };
    let mut cases = vec![p_minus(1), p_minus(0), [0xffu8; 32]];
    for s in 0u8..20 {
        let mut b = [0u8; 32];
        b[0] = s;
        cases.push(b);
        let mut c = b;
        c[31] = 0x80;
        cases.push(c);
    }
    let mut p1 = p_minus(0);
    p1[0] = 0xee;
    cases.push(p1);
    for b in cases {
        check_all(b);
    }
}

/// Random inputs, from a fixed xorshift seed. About half of the even values below p decode.
#[test]
fn random_inputs() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let mut accepted = 0;
    for _ in 0..2000 {
        let mut b = [0u8; 32];
        for c in b.chunks_mut(8) { c.copy_from_slice(&next().to_le_bytes()); }
        b[31] &= 0x7f;
        b[0] &= 0xfe;
        if check_all(b).is_some() { accepted += 1; }
    }
    assert!(accepted > 500, "only {accepted} accepted");
}

/// `encode` on tuples that `decode` does not return: decoded points scaled by a nonzero
/// factor, and random tuples, which are in general not on the curve.
#[test]
fn encode_other_tuples() {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let mut bytes = || {
        let mut b = [0u8; 32];
        for c in b.chunks_mut(8) { c.copy_from_slice(&next().to_le_bytes()); }
        b[31] &= 0x7f;
        b
    };
    for b in vectors::MULTIPLES.iter() {
        let c = port_decode(*b).expect("an RFC multiple decodes");
        check_encode(c);
        for _ in 0..20 {
            let l = bytes();
            check_encode(scale(c, l));
            // A nonzero scale gives the same group element, so the same bytes.
            if spec_fe_bytes(spec_fe(l)) != [0u8; 32] {
                assert_eq!(port_encode(scale(c, l)), *b);
            }
        }
    }
    for _ in 0..500 {
        let c = [bytes(), bytes(), bytes(), bytes()];
        check_encode(c);
    }
}

fn hex32(s: &str) -> [u8; 32] {
    let mut r = [0u8; 32];
    for i in 0..32 { r[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap(); }
    r
}

/// RFC 9496 A.4: the port's `sqrt_ratio_m1` on the six vectors. The spec and dalek keep
/// this function private, so only the port is tested here.
#[test]
fn rfc9496_sqrt_ratio() {
    for (u, v, was_square, r) in vectors::SQRT_RATIO.iter() {
        let (w, x) = sqrt_ratio_m1(fe_from_bytes(hex32(u)), fe_from_bytes(hex32(v)));
        assert_eq!((w, fe_to_bytes(x)), (*was_square, hex32(r)), "u = {u}, v = {v}");
    }
}
