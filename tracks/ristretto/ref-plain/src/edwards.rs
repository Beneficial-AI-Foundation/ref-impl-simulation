//! Hand port of `point_add`, `point_identity` and `point_mul` from hacspec/specs
//! edwards25519/src/edwards25519.rs (commit c511110d) to plain Rust. Field arithmetic is
//! behind the opaque `field` module, and scalars behind the opaque `scalar` module. The
//! order of the field operations is the order of the spec.
use crate::field::*;
use crate::scalar::*;

/// hacspec: `EdPoint`, extended coordinates `(X, Y, Z, T)`.
pub type EdPoint = (Fe, Fe, Fe, Fe);

/// hacspec `point_add`. The spec decodes `CONSTANT_D`, which has the same little-endian
/// bytes as the Ristretto `D`, so `crate::d()` gives the same value.
pub fn point_add(p: EdPoint, q: EdPoint) -> EdPoint {
    let d_c = crate::d();
    let two = fe_lit(2);

    let (x1, y1, z1, t1) = p;
    let (x2, y2, z2, t2) = q;
    let a = fe_mul(fe_sub(y1, x1), fe_sub(y2, x2));
    let b = fe_mul(fe_add(y1, x1), fe_add(y2, x2));
    let c = fe_mul(fe_mul(fe_mul(t1, two), d_c), t2);
    let d = fe_mul(fe_mul(z1, two), z2);
    let e = fe_sub(b, a);
    let f = fe_sub(d, c);
    let g = fe_add(d, c);
    let h = fe_add(b, a);
    let x3 = fe_mul(e, f);
    let y3 = fe_mul(g, h);
    let t3 = fe_mul(e, h);
    let z3 = fe_mul(f, g);
    (x3, y3, z3, t3)
}

/// hacspec `point_identity`.
pub fn point_identity() -> EdPoint {
    (fe_lit(0), fe_lit(1), fe_lit(1), fe_lit(0))
}

/// hacspec `point_mul`. The `for` loop over the bits is a `while` loop.
pub fn point_mul(s: Scalar, p: EdPoint) -> EdPoint {
    let mut p = p;
    let mut q = point_identity();
    let mut i = 0;
    while i < 256 {
        if sc_bit(s, i) {
            q = point_add(q, p);
        }
        p = point_add(p, p);
        i += 1;
    }
    q
}
