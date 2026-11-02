//! Edge inputs for the trusted boundary of track B. `lean/Sim/RefVectors.lean` checks the
//! same inputs and outputs on the Lean reference with the `ZMod p` field model.

use x25519_ref::x25519_scalarmult;

fn h(s: &str) -> [u8; 32] {
    let mut o = [0u8; 32];
    for i in 0..32 {
        o[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
    }
    o
}

// The scalar and u-coordinate of RFC 7748 section 5.2, vector 1.
const K: &str = "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4";
const U: &str = "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c";

fn x(u: &str) -> [u8; 32] {
    x25519_scalarmult(h(K), h(u))
}

#[test]
fn low_order_inputs_give_zero() {
    for u in [
        "0000000000000000000000000000000000000000000000000000000000000000", // 0
        "0100000000000000000000000000000000000000000000000000000000000000", // 1
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", // p - 1
        "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", // p
        "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", // p + 1
        "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800", // order 8
    ] {
        assert_eq!(x(u), [0u8; 32], "u = {u}");
    }
}

#[test]
fn top_bit_of_u_is_ignored() {
    let mut u = h(U);
    u[31] |= 0x80;
    assert_eq!(x25519_scalarmult(h(K), u), x(U));
}

#[test]
fn noncanonical_u_is_reduced() {
    // p + 9 against 9, and 2^255 - 1 = p + 18 against 18.
    assert_eq!(
        x("f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        x("0900000000000000000000000000000000000000000000000000000000000000")
    );
    assert_eq!(
        x("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        x("1200000000000000000000000000000000000000000000000000000000000000")
    );
}

#[test]
fn clamped_scalar_bits_are_ignored() {
    let mut k = h(K);
    k[0] ^= 0x07;
    k[31] ^= 0xc0;
    assert_eq!(x25519_scalarmult(k, h(U)), x(U));
}

// Outputs computed with this port and checked against OpenSSL's X25519.
const EDGE_OUTPUTS: [(&str, &str); 3] = [
    (
        "0900000000000000000000000000000000000000000000000000000000000000",
        "1c9fd88f45606d932a80c71824ae151d15d73e77de38e8e000852e614fae7019",
    ),
    (
        "1200000000000000000000000000000000000000000000000000000000000000",
        "76b00406ce7e87774c0038dd8d89b188047977f8828ca1dcb8f98bb5d5d0cf48",
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "76b00406ce7e87774c0038dd8d89b188047977f8828ca1dcb8f98bb5d5d0cf48",
    ),
];

#[test]
fn fixed_outputs() {
    for (u, r) in EDGE_OUTPUTS {
        assert_eq!(x(u), h(r), "u = {u}");
    }
}
