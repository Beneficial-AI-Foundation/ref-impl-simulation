//! Hand port of hacspec/specs curve25519/src/curve25519.rs (RFC 7748 X25519)
//! to plain Rust. Field arithmetic is behind the opaque `field` module.
pub mod field;
use field::*;

pub type Point = (Fe, Fe);
pub type SerializedPoint = [u8; 32];
pub type SerializedScalar = [u8; 32];

pub fn mask_scalar(s: SerializedScalar) -> SerializedScalar {
    let mut k = s;
    k[0] = k[0] & 248u8;
    k[31] = k[31] & 127u8;
    k[31] = k[31] | 64u8;
    k
}

/// hacspec: `Scalar::from_byte_seq_le(mask_scalar(s))`, with Scalar = nat_mod 2^255.
/// The masked value is < 2^255, so the scalar is the masked bytes themselves.
pub fn decode_scalar(s: SerializedScalar) -> SerializedScalar {
    mask_scalar(s)
}

/// hacspec: `k.bit(i)` on the scalar.
pub fn scalar_bit(k: &SerializedScalar, i: usize) -> bool {
    (k[i / 8] >> (i % 8)) & 1u8 == 1u8
}

pub fn decode_point(u: SerializedPoint) -> Point {
    let mut u_ = u;
    u_[31] = u_[31] & 127u8;
    (fe_from_bytes(u_), fe_lit(1))
}

pub fn encode_point(p: Point) -> SerializedPoint {
    let (x, y) = p;
    let b = fe_mul(x, fe_inv(y));
    fe_to_bytes(b)
}

pub fn point_add_and_double(q: Point, np: (Point, Point)) -> (Point, Point) {
    let (nq, nqp1) = np;
    let (x_1, _z_1) = q;
    let (x_2, z_2) = nq;
    let (x_3, z_3) = nqp1;
    let a = fe_add(x_2, z_2);
    let aa = fe_sq(a);
    let b = fe_sub(x_2, z_2);
    let bb = fe_mul(b, b);
    let e = fe_sub(aa, bb);
    let c = fe_add(x_3, z_3);
    let d = fe_sub(x_3, z_3);
    let da = fe_mul(d, a);
    let cb = fe_mul(c, b);

    let x_3 = fe_sq(fe_add(da, cb));
    let z_3 = fe_mul(x_1, fe_sq(fe_sub(da, cb)));
    let x_2 = fe_mul(aa, bb);
    let e121665 = fe_lit(121_665);
    let z_2 = fe_mul(e, fe_add(aa, fe_mul(e121665, e)));
    ((x_2, z_2), (x_3, z_3))
}

pub fn swap(x: (Point, Point)) -> (Point, Point) {
    let (x0, x1) = x;
    (x1, x0)
}

/// One iteration of the hacspec ladder loop body.
pub fn ladder_step(k: &SerializedScalar, init: Point, acc: (Point, Point), i: usize) -> (Point, Point) {
    if scalar_bit(k, 255 - i) {
        swap(point_add_and_double(init, swap(acc)))
    } else {
        point_add_and_double(init, acc)
    }
}

pub fn montgomery_ladder(k: SerializedScalar, init: Point) -> Point {
    let inf = (fe_lit(1), fe_lit(0));
    let mut acc: (Point, Point) = (inf, init);
    acc = ladder_loop(&k, init, acc, 0);
    acc.0
}

/// The hacspec `for i in 0..256` loop, as tail recursion (Aeneas workaround).
pub fn ladder_loop(k: &SerializedScalar, init: Point, acc: (Point, Point), i: usize) -> (Point, Point) {
    if i < 256 {
        ladder_loop(k, init, ladder_step(k, init, acc, i), i + 1)
    } else {
        acc
    }
}

pub fn x25519_scalarmult(s: SerializedScalar, p: SerializedPoint) -> SerializedPoint {
    let s_ = decode_scalar(s);
    let p_ = decode_point(p);
    let r = montgomery_ladder(s_, p_);
    encode_point(r)
}

pub fn x25519_secret_to_public(s: SerializedScalar) -> SerializedPoint {
    let mut base = [0u8; 32];
    base[0] = 0x09u8;
    x25519_scalarmult(s, base)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn h(s: &str) -> [u8; 32] {
        let mut o = [0u8; 32];
        for i in 0..32 { o[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap(); }
        o
    }
    #[test]
    fn rfc7748_5_2_vector1() {
        let k = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
        let u = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
        let r = h("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552");
        assert_eq!(x25519_scalarmult(k, u), r);
    }
    #[test]
    fn rfc7748_6_1_alice_public() {
        let a = h("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
        let pa = h("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a");
        assert_eq!(x25519_secret_to_public(a), pa);
    }
}
