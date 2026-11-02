#!/usr/bin/env python3
"""Compare the functions on the path of `mul_clamped_refines` between two dalek trees.

Usage: compare-dalek5.py COPY_DIR OTHER_DIR

COPY_DIR is the copy that this track extracts (`real-dalek/curve25519-dalek`). OTHER_DIR
is another curve25519-dalek source tree, for example 5.0.0 from the cargo registry. The
script strips comments and blank lines and compares each function body. It prints `==`
for an identical body and a diff otherwise. It exits 1 if a function is missing.
"""

import difflib
import re
import sys

FUNCTIONS = [
    ("src/backend/serial/u64/field.rs", "fn add_assign(&mut self, _rhs: &'a FieldElement51)"),
    ("src/backend/serial/u64/field.rs", "fn add(self, _rhs: &'a FieldElement51) -> FieldElement51"),
    ("src/backend/serial/u64/field.rs", "fn sub(self, _rhs: &'a FieldElement51) -> FieldElement51"),
    ("src/backend/serial/u64/field.rs", "fn mul(self, _rhs: &'a FieldElement51) -> FieldElement51"),
    ("src/backend/serial/u64/field.rs", "fn conditional_select("),
    ("src/backend/serial/u64/field.rs", "pub const ZERO"),
    ("src/backend/serial/u64/field.rs", "pub const ONE"),
    ("src/backend/serial/u64/field.rs", "fn reduce(mut limbs: [u64; 5])"),
    ("src/backend/serial/u64/field.rs", "pub const fn from_bytes(bytes: &[u8; 32])"),
    ("src/backend/serial/u64/field.rs", "pub fn to_bytes(self) -> [u8; 32]"),
    ("src/backend/serial/u64/field.rs", "pub fn pow2k(&self, mut k: u32)"),
    ("src/backend/serial/u64/field.rs", "pub fn square(&self) -> FieldElement51"),
    ("src/backend/serial/u64/constants.rs", "pub(crate) const APLUS2_OVER_FOUR"),
    ("src/field.rs", "fn pow22501(&self)"),
    ("src/field.rs", "pub(crate) fn invert(&self)"),
    ("src/montgomery.rs", "pub fn mul_clamped(self, bytes: [u8; 32])"),
    ("src/montgomery.rs", "fn identity() -> ProjectivePoint"),
    ("src/montgomery.rs", "fn conditional_select("),
    ("src/montgomery.rs", "pub fn as_affine(&self) -> MontgomeryPoint"),
    ("src/montgomery.rs", "fn differential_add_and_double("),
    ("src/montgomery.rs", "impl Mul<&MontgomeryPoint> for &Scalar"),
    ("src/montgomery.rs", "fn mul(self, scalar: &Scalar) -> MontgomeryPoint"),
    ("src/montgomery.rs", "pub fn mul_bits_be(&self, bits: impl Iterator<Item = bool>)"),
    ("src/scalar.rs", "pub const fn clamp_integer(mut bytes: [u8; 32])"),
    ("src/scalar.rs", "pub const fn as_bytes(&self)"),
    ("src/scalar.rs", "pub(crate) fn bits_le(&self)"),
    ("src/macros.rs", "macro_rules! define_mul_variants"),
]


def body(path, sig):
    """The text from `sig` to the end of its first balanced `{ }` or `;`, without comments."""
    try:
        s = open(path, encoding="utf-8").read()
    except FileNotFoundError:
        return None
    i = s.find(sig)
    if i < 0:
        return None
    j = i
    while s[j] not in "{;":
        j += 1
    if s[j] == "{":
        depth = 0
        while True:
            depth += {"{": 1, "}": -1}.get(s[j], 0)
            if depth == 0:
                break
            j += 1
    text = s[s.rfind("\n", 0, i) + 1 : j + 1]
    lines = (re.sub(r"//.*", "", line).strip() for line in text.split("\n"))
    return [line for line in lines if line]


def main(copy_dir, other_dir):
    missing = 0
    for path, sig in FUNCTIONS:
        a, b = body(f"{copy_dir}/{path}", sig), body(f"{other_dir}/{path}", sig)
        if a is None or b is None:
            print(f"?? {path} :: {sig}: missing in {'copy' if a is None else 'other'}")
            missing += 1
        elif a == b:
            print(f"== {path} :: {sig}")
        else:
            print(f"!= {path} :: {sig}")
            for line in difflib.unified_diff(a, b, "copy", "other", lineterm="", n=0):
                print("     " + line)
    return 1 if missing else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
