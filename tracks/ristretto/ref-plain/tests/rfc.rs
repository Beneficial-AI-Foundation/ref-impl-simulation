//! RFC 9496 test vectors and differential tests against the unchanged hacspec spec and
//! curve25519-dalek 5.0.0.
mod vectors;
use curve25519_dalek::ristretto::CompressedRistretto;
use ristretto_ref::{decode, encode, DECODING_ERROR};

/// The unchanged spec: `Some(encode(decode(b)))` or `None`.
fn spec_roundtrip(b: [u8; 32]) -> Option<[u8; 32]> {
    use hacspec_ristretto as h;
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

fn check_all(b: [u8; 32]) -> Option<[u8; 32]> {
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
