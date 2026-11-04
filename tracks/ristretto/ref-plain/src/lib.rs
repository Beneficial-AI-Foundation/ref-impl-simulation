//! Hand port of `decode`, `encode` and their helpers from hacspec/specs
//! ristretto/src/ristretto.rs (commit c511110d) to plain Rust. Field arithmetic is
//! behind the opaque `field` module. The order of the field operations is the order of
//! the spec. Each function names the spec function it ports. The module `edwards` ports
//! the scalar multiplication of hacspec/specs edwards25519.
pub mod edwards;
pub mod field;
pub mod scalar;
use field::*;

/// hacspec: `(FieldElement, FieldElement, FieldElement, FieldElement)`.
pub type RistrettoPoint = (Fe, Fe, Fe, Fe);
/// hacspec: `Result<RistrettoPoint, u8>`.
pub type DecodeResult = Result<RistrettoPoint, u8>;
/// hacspec: `bytes!(RistrettoPointEncoded, 32)`.
pub type RistrettoPointEncoded = [u8; 32];

pub const DECODING_ERROR: u8 = 20u8;

/// hacspec `D()`, as little-endian bytes.
pub fn d() -> Fe {
    fe_from_bytes([
        0xa3, 0x78, 0x59, 0x13, 0xca, 0x4d, 0xeb, 0x75, 0xab, 0xd8, 0x41, 0x41, 0x4d, 0x0a,
        0x70, 0x00, 0x98, 0xe8, 0x79, 0x77, 0x79, 0x40, 0xc7, 0x8c, 0x73, 0xfe, 0x6f, 0x2b,
        0xee, 0x6c, 0x03, 0x52,
    ])
}

/// hacspec `SQRT_M1()`, as little-endian bytes.
pub fn sqrt_m1() -> Fe {
    fe_from_bytes([
        0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4, 0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18,
        0x43, 0x2f, 0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b, 0x0b, 0xdf, 0xc1, 0x4f,
        0x80, 0x24, 0x83, 0x2b,
    ])
}

/// hacspec `INVSQRT_A_MINUS_D()`, as little-endian bytes.
pub fn invsqrt_a_minus_d() -> Fe {
    fe_from_bytes([
        0xea, 0x40, 0x5d, 0x80, 0xaa, 0xfd, 0xc8, 0x99, 0xbe, 0x72, 0x41, 0x5a, 0x17, 0x16,
        0x2f, 0x9d, 0x40, 0xd8, 0x01, 0xfe, 0x91, 0x7b, 0xc2, 0x16, 0xa2, 0xfc, 0xaf, 0xcf,
        0x05, 0x89, 0x6c, 0x78,
    ])
}

/// hacspec `geq_p`. The `for` loop over the indices is a `while` loop.
pub fn geq_p(x: [u8; 32]) -> bool {
    let p_seq: [u8; 32] = [
        0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0x7f,
    ];
    let mut res = true;
    let mut index = 0;
    while index < 32 {
        let x_index = x[index];
        let p_index = p_seq[index];
        if x_index != p_index {
            res = x_index > p_index;
        }
        index += 1;
    }
    res
}

/// hacspec `is_negative`.
pub fn is_negative(e: Fe) -> bool {
    fe_is_negative(e)
}

/// hacspec `eq`.
pub fn eq(u: Fe, v: Fe) -> bool {
    fe_eq(u, v)
}

/// hacspec `select`.
pub fn select(u: Fe, cond: bool, v: Fe) -> Fe {
    if cond { u } else { v }
}

/// hacspec `neg_fe`.
pub fn neg_fe(u: Fe) -> Fe {
    fe_sub(fe_lit(0), u)
}

/// hacspec `abs`.
pub fn abs(u: Fe) -> Fe {
    select(neg_fe(u), is_negative(u), u)
}

/// hacspec `sqrt_ratio_m1`.
pub fn sqrt_ratio_m1(u: Fe, v: Fe) -> (bool, Fe) {
    let v3 = fe_mul(fe_sq(v), v);
    let v7 = fe_mul(fe_sq(v3), v);
    let mut r = fe_mul(fe_mul(u, v3), fe_pow_p58(fe_mul(u, v7)));
    let check = fe_mul(v, fe_sq(r));

    let correct_sign_sqrt = eq(check, u);
    let flipped_sign_sqrt = eq(check, neg_fe(u));
    let flipped_sign_sqrt_i = eq(check, fe_mul(neg_fe(u), sqrt_m1()));

    let r_prime = fe_mul(sqrt_m1(), r);
    r = select(r_prime, flipped_sign_sqrt || flipped_sign_sqrt_i, r);

    // Choose the nonnegative square root.
    r = abs(r);

    let was_square = correct_sign_sqrt || flipped_sign_sqrt;

    (was_square, r)
}

/// hacspec `encode`.
pub fn encode(u: RistrettoPoint) -> RistrettoPointEncoded {
    let (x0, y0, z0, t0) = u;

    let u1 = fe_mul(fe_add(z0, y0), fe_sub(z0, y0));
    let u2 = fe_mul(x0, y0);

    // Ignore was_square since this is always square
    let (_, invsqrt) = sqrt_ratio_m1(fe_lit(1), fe_mul(u1, fe_sq(u2)));

    let den1 = fe_mul(invsqrt, u1);
    let den2 = fe_mul(invsqrt, u2);
    let z_inv = fe_mul(fe_mul(den1, den2), t0);

    let ix0 = fe_mul(x0, sqrt_m1());
    let iy0 = fe_mul(y0, sqrt_m1());
    let enchanted_denominator = fe_mul(den1, invsqrt_a_minus_d());

    let rotate = is_negative(fe_mul(t0, z_inv));

    let x = select(iy0, rotate, x0);
    let mut y = select(ix0, rotate, y0);
    let z = z0;
    let den_inv = select(enchanted_denominator, rotate, den2);

    y = select(neg_fe(y), is_negative(fe_mul(x, z_inv)), y);

    let s = abs(fe_mul(den_inv, fe_sub(z, y)));

    fe_to_bytes(s)
}

/// hacspec `decode`.
pub fn decode(u: RistrettoPointEncoded) -> DecodeResult {
    let mut ret = DecodeResult::Err(DECODING_ERROR);

    let s = fe_from_bytes(u);

    if !geq_p(u) && !is_negative(s) {
        let one = fe_lit(1);
        let ss = fe_sq(s);
        let u1 = fe_sub(one, ss);
        let u2 = fe_add(one, ss);
        let u2_sqr = fe_sq(u2);

        let v = fe_sub(neg_fe(fe_mul(d(), fe_sq(u1))), u2_sqr);

        let (was_square, invsqrt) = sqrt_ratio_m1(one, fe_mul(v, u2_sqr));

        let den_x = fe_mul(invsqrt, u2);
        let den_y = fe_mul(fe_mul(invsqrt, den_x), v);

        let x = abs(fe_mul(fe_add(s, s), den_x));
        let y = fe_mul(u1, den_y);
        let t = fe_mul(x, y);

        if !(!was_square || is_negative(t) || eq(y, fe_lit(0))) {
            ret = DecodeResult::Ok((x, y, one, t));
        }
    }
    ret
}
