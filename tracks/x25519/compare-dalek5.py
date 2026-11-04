#!/usr/bin/env python3
"""Check that the proved trees agree with the libsignal versions on the paths of the theorems.

Usage: compare-dalek5.py [--self-test] COPY_DIR OTHER_DIR X_COPY_DIR X_OTHER_DIR

COPY_DIR is the curve25519-dalek copy that this track extracts (`real-dalek/curve25519-dalek`).
OTHER_DIR is curve25519-dalek 5.0.0, the version that libsignal uses. X_COPY_DIR is the
x25519-dalek copy that this track extracts (`real-x25519/x25519-dalek`, version 2.0.1).
X_OTHER_DIR is x25519-dalek 3.0.0, the version that libsignal uses. For each item in `ITEMS`
and `X_ITEMS`, the script extracts its text from both trees, removes comments and blank
lines, and compares the results. An item is a function, a constant, a static, a struct, a
macro or a macro call, found by its `impl` block and its name. For a struct, the
attribute lines (`#[...]`) right above it belong to it.

The script prints `==` for an identical item and `!=` with the diff otherwise. It exits 1
if an item is missing or ambiguous in either tree, or if a diff differs from the reviewed
diff in `EXPECTED`. With `--self-test`, it also changes each item of OTHER_DIR in memory
and checks that the comparison reports the change.
"""

import difflib
import re
import sys

FIELD = "src/backend/serial/u64/field.rs"
MONT = "src/montgomery.rs"
SCALAR = "src/scalar.rs"
EDW = "src/edwards.rs"
CM = "src/backend/serial/curve_models/mod.rs"
WIN = "src/window.rs"
U64C = "src/backend/serial/u64/constants.rs"

# Files that 5.0.0 moved: path in the copy -> path in 5.0.0.
MOVED = {
    "src/backend/serial/curve_models/mod.rs": "src/backend/serial/curve_models.rs",
}

# (file, impl block, kind, name). The impl block is a list of substrings that must all occur
# in the `impl` header line, or None for an item outside any `impl` block.
ITEMS = [
    (FIELD, ["AddAssign<", "for FieldElement51"], "fn", "add_assign"),
    (FIELD, ["Add<", "for &FieldElement51"], "fn", "add"),
    (FIELD, ["Sub<", "for &FieldElement51"], "fn", "sub"),
    (FIELD, ["Mul<", "for &FieldElement51"], "fn", "mul"),
    (FIELD, ["ConditionallySelectable for FieldElement51"], "fn", "conditional_select"),
    (FIELD, ["impl FieldElement51 {"], "fn", "from_limbs"),
    (FIELD, ["impl FieldElement51 {"], "const", "ZERO"),
    (FIELD, ["impl FieldElement51 {"], "const", "ONE"),
    (FIELD, ["impl FieldElement51 {"], "fn", "reduce"),
    (FIELD, ["impl FieldElement51 {"], "fn", "from_bytes"),
    (FIELD, ["impl FieldElement51 {"], "fn", "to_bytes"),
    (FIELD, ["impl FieldElement51 {"], "fn", "pow2k"),
    (FIELD, ["impl FieldElement51 {"], "fn", "square"),
    ("src/backend/serial/u64/constants.rs", None, "const", "APLUS2_OVER_FOUR"),
    ("src/field.rs", ["impl FieldElement {"], "fn", "pow22501"),
    ("src/field.rs", ["impl FieldElement {"], "fn", "invert"),
    (MONT, ["impl MontgomeryPoint {"], "fn", "mul_clamped"),
    (MONT, ["impl MontgomeryPoint {"], "fn", "mul_bits_be"),
    (MONT, ["impl MontgomeryPoint {"], "fn", "to_bytes"),
    (MONT, ["impl MontgomeryPoint {"], "fn", "as_bytes"),
    (MONT, ["Identity for ProjectivePoint"], "fn", "identity"),
    (MONT, ["ConditionallySelectable for ProjectivePoint"], "fn", "conditional_select"),
    (MONT, ["impl ProjectivePoint {"], "fn", "as_affine"),
    (MONT, None, "fn", "differential_add_and_double"),
    (MONT, ["Mul<&Scalar> for &MontgomeryPoint"], "fn", "mul"),
    (MONT, ["Mul<&MontgomeryPoint> for &Scalar"], "fn", "mul"),
    (SCALAR, ["impl Scalar {"], "fn", "as_bytes"),
    (SCALAR, ["impl Scalar {"], "fn", "bits_le"),
    (SCALAR, None, "fn", "clamp_integer"),
    ("src/macros.rs", None, "macro", "define_mul_variants"),
    # Public-key derivation (steps X1 and X2): `mul_base_clamped` of the Montgomery curve and
    # of the Edwards curve, the table multiplication and the map back to Montgomery.
    (MONT, ["impl MontgomeryPoint {"], "fn", "mul_base"),
    (MONT, ["impl MontgomeryPoint {"], "fn", "mul_base_clamped"),
    (MONT, ["ConstantTimeEq for MontgomeryPoint"], "fn", "ct_eq"),
    (MONT, ["Identity for MontgomeryPoint"], "fn", "identity"),
    ("src/traits.rs", ["IsIdentity for T"], "fn", "is_identity"),
    (EDW, ["impl EdwardsPoint {"], "fn", "mul_base"),
    (EDW, ["impl EdwardsPoint {"], "fn", "mul_base_clamped"),
    (EDW, ["impl EdwardsPoint {"], "fn", "to_montgomery"),
    (EDW, ["impl EdwardsPoint {"], "fn", "mul_by_pow_2"),
    (EDW, ["impl EdwardsPoint {"], "fn", "double"),
    (EDW, ["impl EdwardsPoint {"], "fn", "as_affine_niels"),
    (EDW, ["ConstantTimeEq for EdwardsPoint"], "fn", "ct_eq"),
    (EDW, ["Identity for EdwardsPoint"], "fn", "identity"),
    (EDW, None, "struct", "EdwardsPoint"),
    (EDW, None, "macro", "impl_basepoint_table"),
    (EDW, None, "call", "impl_basepoint_table:EdwardsBasepointTable"),
    (WIN, None, "macro", "impl_lookup_table"),
    (WIN, None, "call", "impl_lookup_table:LookupTable"),
    (SCALAR, ["impl Scalar {"], "fn", "as_radix_16"),
    (SCALAR, ["impl Scalar {"], "fn", "as_radix_2w"),
    (CM, ["Identity for AffineNielsPoint"], "fn", "identity"),
    (CM, ["ConditionallySelectable for AffineNielsPoint"], "fn", "conditional_select"),
    (CM, ["ConditionallySelectable for AffineNielsPoint"], "fn", "conditional_assign"),
    (CM, ["Neg for &AffineNielsPoint"], "fn", "neg"),
    (CM, ["Neg for AffineNielsPoint"], "fn", "neg"),
    (CM, ["Add<", "AffineNielsPoint> for &EdwardsPoint"], "fn", "add"),
    (CM, ["impl ProjectivePoint {"], "fn", "as_extended"),
    (CM, ["impl ProjectivePoint {"], "fn", "double"),
    (CM, ["impl CompletedPoint {"], "fn", "as_projective"),
    (CM, ["impl CompletedPoint {"], "fn", "as_extended"),
    (CM, None, "struct", "AffineNielsPoint"),
    (U64C, None, "const", "EDWARDS_D2"),
    (U64C, None, "const", "ED25519_BASEPOINT_POINT"),
    (U64C, None, "static", "ED25519_BASEPOINT_TABLE"),
    (U64C, None, "static", "ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"),
    # `was_contributory` (step X1): the field `ct_eq` that `MontgomeryPoint::ct_eq` calls.
    ("src/field.rs", ["ConstantTimeEq for FieldElement"], "fn", "ct_eq"),
]

# The items of x25519-dalek on the paths of `x25519_refines` and of the `diffie_hellman`
# theorems. The two `from` functions are not in the extraction (README, section 2,
# "Real wrapper").
X_ITEMS = [
    ("src/x25519.rs", None, "fn", "x25519"),
    ("src/x25519.rs", ["impl StaticSecret {"], "fn", "diffie_hellman"),
    ("src/x25519.rs", ["impl SharedSecret {"], "fn", "as_bytes"),
    ("src/x25519.rs", ["From<[u8; 32]> for StaticSecret"], "fn", "from"),
    ("src/x25519.rs", ["From<[u8; 32]> for PublicKey"], "fn", "from"),
    # Steps X1 and X2: the other two secret wrappers, public-key derivation and the
    # contributory check.
    ("src/x25519.rs", ["impl EphemeralSecret {"], "fn", "diffie_hellman"),
    ("src/x25519.rs", ["impl ReusableSecret {"], "fn", "diffie_hellman"),
    ("src/x25519.rs", ["From<&'a EphemeralSecret> for PublicKey"], "fn", "from"),
    ("src/x25519.rs", ["From<&'a ReusableSecret> for PublicKey"], "fn", "from"),
    ("src/x25519.rs", ["From<&'a StaticSecret> for PublicKey"], "fn", "from"),
    ("src/x25519.rs", ["impl SharedSecret {"], "fn", "was_contributory"),
    ("src/x25519.rs", ["impl SharedSecret {"], "fn", "to_bytes"),
    ("src/x25519.rs", ["impl StaticSecret {"], "fn", "to_bytes"),
    ("src/x25519.rs", ["impl StaticSecret {"], "fn", "as_bytes"),
    ("src/x25519.rs", ["impl PublicKey {"], "fn", "to_bytes"),
    ("src/x25519.rs", ["impl PublicKey {"], "fn", "as_bytes"),
    ("src/x25519.rs", None, "struct", "PublicKey"),
    ("src/x25519.rs", None, "struct", "EphemeralSecret"),
    ("src/x25519.rs", None, "struct", "ReusableSecret"),
    ("src/x25519.rs", None, "struct", "StaticSecret"),
    ("src/x25519.rs", None, "struct", "SharedSecret"),
    ("src/x25519.rs", None, "const", "X25519_BASEPOINT_BYTES"),
]

# Items of the copy that 5.0.0 does not have, as (file, first impl string, name). 5.0.0
# keeps only `Neg for &AffineNielsPoint`. Its `select` calls `conditional_negate`, so nothing
# calls the owned `neg` any more.
ABSENT = {
    (CM, "Neg for AffineNielsPoint", "neg"),
}

# The reviewed diffs, as printed by this script: the extraction edits of
# `curve25519-dalek-lean-verify`. Any other difference fails the check.
EXPECTED = {
    (FIELD, "add_assign"): [
        "@@ -2,2 +2 @@",
        "-let mut i = 0;",
        "-while i < 5 {",
        "+for i in 0..5 {",
        "@@ -5 +3,0 @@",
        "-i += 1;",
    ],
    (FIELD, "pow2k"): [
        "@@ -8 +8 @@",
        "-while k > 0 {",
        "+loop {",
        "@@ -15,0 +16,5 @@",
        "+debug_assert!(a[0] < (1 << 54));",
        "+debug_assert!(a[1] < (1 << 54));",
        "+debug_assert!(a[2] < (1 << 54));",
        "+debug_assert!(a[3] < (1 << 54));",
        "+debug_assert!(a[4] < (1 << 54));",
        "@@ -30,0 +36,3 @@",
        "+if k == 0 {",
        "+break;",
        "+}",
    ],
    (MONT, "mul_bits_be"): [
        "@@ -10 +10 @@",
        "-let choice: u8 = (prev_bit != cur_bit) as u8;",
        "+let choice: u8 = (prev_bit ^ cur_bit) as u8;",
    ],
    # The copy inlines `mul_bits_be(scalar.bits_le().rev().skip(1))` as an index loop.
    ("Mul<&Scalar> for &MontgomeryPoint", "mul"): [
    "@@ -2,19 +2 @@",
    "-let affine_u = FieldElement::from_bytes(&self.0);",
    "-let mut x0 = ProjectivePoint::identity();",
    "-let mut x1 = ProjectivePoint {",
    "-U: affine_u,",
    "-W: FieldElement::ONE,",
    "-};",
    "-let scalar_bytes = scalar.as_bytes();",
    "-let mut prev_bit = false;",
    "-let mut i: isize = 254;",
    "-while i >= 0 {",
    "-let byte_idx = (i >> 3) as usize;",
    "-let bit_idx = (i & 7) as usize;",
    "-let cur_bit = ((scalar_bytes[byte_idx] >> bit_idx) & 1u8) == 1u8;",
    "-let choice: u8 = (prev_bit != cur_bit) as u8;",
    "-debug_assert!(choice == 0 || choice == 1);",
    "-ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());",
    "-differential_add_and_double(&mut x0, &mut x1, &affine_u);",
    "-prev_bit = cur_bit;",
    "-i -= 1;",
    "+self.mul_bits_be(scalar.bits_le().rev().skip(1))",
    "@@ -22,5 +3,0 @@",
    "-ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(prev_bit as u8));",
    "-#[cfg(feature = \"zeroize\")]",
    "-prev_bit.zeroize();",
    "-x0.as_affine()",
    "-}",
    ],
    # Extraction edit of the copy: a `while` loop with a counter, as in `add_assign`.
    (EDW, "mul_by_pow_2"): [
        "@@ -5,2 +5 @@",
        "-let mut i = 0;",
        "-while i < k - 1 {",
        "+for _ in 0..(k - 1) {",
        "@@ -9 +7,0 @@",
        "-i += 1;",
    ],
    # 5.0.0 calls `conditional_negate` of `subtle`. Its default method (`subtle` 2.6.1) is
    # `let self_neg = -(&*self); self.conditional_assign(&self_neg, choice)`. The copy writes
    # this out with the owned `neg`, which 5.0.0 no longer has (`ABSENT`).
    (WIN, "impl_lookup_table"): [
        "@@ -7 +7 @@",
        "-T: Identity + ConditionallySelectable + Copy + Neg<Output = T>,",
        "+T: Identity + ConditionallySelectable + ConditionallyNegatable,",
        "@@ -20,2 +20 @@",
        "-let t_neg = -t;",
        "-t.conditional_assign(&t_neg, neg_mask);",
        "+t.conditional_negate(neg_mask);",
    ],
    # Extraction edit of the copy: two `while` loops with counters.
    (SCALAR, "as_radix_16"): [
        "@@ -13,2 +13 @@",
        "-let mut i = 0;",
        "-while i < 32 {",
        "+for i in 0..32 {",
        "@@ -17 +15,0 @@",
        "-i += 1;",
        "@@ -19,2 +17 @@",
        "-let mut i = 0;",
        "-while i < 63 {",
        "+for i in 0..63 {",
        "@@ -24 +20,0 @@",
        "-i += 1;",
    ],
    # Extraction edits of the copy: `div_ceil` and `match` written as `/` and `if`.
    (SCALAR, "as_radix_2w"): [
        "@@ -13 +13 @@",
        "-let digits_count = (256 + w - 1) / w;",
        "+let digits_count = 256_usize.div_ceil(w);",
        "@@ -28,4 +28,3 @@",
        "-if w == 8 {",
        "-digits[digits_count] += carry as i8;",
        "-} else {",
        "-digits[digits_count - 1] += (carry << w) as i8;",
        "+match w {",
        "+8 => digits[digits_count] += carry as i8,",
        "+_ => digits[digits_count - 1] += (carry << w) as i8,",
    ],
    # x25519-dalek 3.0.0 replaces `derive(Zeroize)` and `zeroize(drop)` by explicit `impl Zeroize`,
    # `impl Drop` and `impl ZeroizeOnDrop` blocks that call `self.0.zeroize()`. Behavior is the
    # same. `PublicKey` has no drop in either version.
    ("src/x25519.rs", "PublicKey"): [
        "@@ -2 +1,0 @@",
        "-#[cfg_attr(feature = \"zeroize\", derive(Zeroize))]",
    ],
    ("src/x25519.rs", "EphemeralSecret"): [
        "@@ -1,2 +0,0 @@",
        "-#[cfg_attr(feature = \"zeroize\", derive(Zeroize))]",
        "-#[cfg_attr(feature = \"zeroize\", zeroize(drop))]",
    ],
    ("src/x25519.rs", "ReusableSecret"): [
        "@@ -2,2 +1,0 @@",
        "-#[cfg_attr(feature = \"zeroize\", derive(Zeroize))]",
        "-#[cfg_attr(feature = \"zeroize\", zeroize(drop))]",
    ],
    ("src/x25519.rs", "StaticSecret"): [
        "@@ -3,2 +2,0 @@",
        "-#[cfg_attr(feature = \"zeroize\", derive(Zeroize))]",
        "-#[cfg_attr(feature = \"zeroize\", zeroize(drop))]",
    ],
    ("src/x25519.rs", "SharedSecret"): [
        "@@ -1,2 +0,0 @@",
        "-#[cfg_attr(feature = \"zeroize\", derive(Zeroize))]",
        "-#[cfg_attr(feature = \"zeroize\", zeroize(drop))]",
    ],
}


class Missing(Exception):
    pass


# Counts of the reviewed outcomes of the last full run: identical, changed, absent in OTHER.
COUNT = {"identical": 0, "changed": 0, "absent": 0}


def lex(src):
    """Return (code, shape). `code` is `src` with comments blanked. `shape` also blanks
    string and character literals. Both keep every newline and the length of `src`."""
    code, shape = list(src), list(src)
    i, n = 0, len(src)

    def blank(a, b, also_code):
        for k in range(a, b):
            if src[k] != "\n":
                shape[k] = " "
                if also_code:
                    code[k] = " "

    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j, True)
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j, True)
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i + 1, j, False)
            i = j + 1
        elif src[i] == "'":
            m = re.match(r"'(?:\\.|[^\\'\n])'", src[i:])
            if m:
                blank(i + 1, i + m.end() - 1, False)
                i += m.end()
            else:
                i += 1  # a lifetime
        else:
            i += 1
    return "".join(code), "".join(shape)


def close(shape, start, opener="{"):
    """Index after the bracket that closes the first `opener` at or after `start`."""
    j = shape.index(opener, start)
    depth = 0
    pairs = {"{": "}", "(": ")", "[": "]"}
    closer = pairs[opener]
    while True:
        if shape[j] == opener:
            depth += 1
        elif shape[j] == closer:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1


def item_end(shape, start, kind):
    """End of the item that starts at `start`: its body for a function, macro or macro call,
    its `;` for a constant or static. A struct ends at its body or, for a tuple struct, at
    its `;`. Brackets in the signature, such as `[u8; 32]`, are skipped."""
    depth, j = 0, start
    while True:
        c = shape[j]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif depth == 0 and c == "{" and kind not in ("const", "static"):
            return close(shape, j)
        elif depth == 0 and c == ";" and kind in ("const", "static", "struct"):
            return j + 1
        elif depth == 0 and c == "{":
            j = close(shape, j) - 1
        j += 1


def with_attributes(shape, start):
    """Start of the line of `start`, moved up over the blank lines and the one-line `#[...]`
    lines above it."""
    ls = shape.rfind("\n", 0, start) + 1
    while ls > 0:
        ps = shape.rfind("\n", 0, ls - 1) + 1
        line = shape[ps:ls - 1].strip()
        if line and not line.startswith("#["):
            break
        ls = ps
    return ls


def locate(shape, impl, kind, name):
    """(start, end) of the item in `shape`."""
    if impl is None:
        scopes = [(0, len(shape))]
    else:
        scopes = [(m.start(), close(shape, m.start()))
                  for m in re.finditer(r"^impl\b[^\n]*", shape, re.M)
                  if all(s in m.group(0) for s in impl)]
        if not scopes:
            raise Missing(f"no impl block {impl}")
    if kind == "macro":
        pattern = rf"^macro_rules!\s+{name}\b"
    elif kind in ("const", "static"):
        pattern = rf"^\s*(?:pub(?:\([^)]*\))?\s+)?{kind}\s+{name}\b"
    elif kind == "struct":
        pattern = rf"^\s*(?:pub(?:\([^)]*\))?\s+)?struct\s+{name}\b"
    elif kind == "call":
        macro, first = name.split(":")
        pattern = rf"^\s*{macro}!\s*\{{\s*Name\s*=\s*{first}\s*,"
    else:
        pattern = rf"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?fn\s+{name}\b"
    if impl is None:
        pattern = pattern.replace(r"^\s*", "^[ \t]*" if kind == "call" else "^")
    hits = [lo + m.start() for lo, hi in scopes
            for m in re.finditer(pattern, shape[lo:hi], re.M)]
    if len(hits) != 1:
        raise Missing(f"{kind} {name}: {len(hits)} matches")
    start = with_attributes(shape, hits[0]) if kind == "struct" else hits[0]
    return start, item_end(shape, hits[0], kind)


def normalized(code, start, end):
    lines = (line.strip() for line in code[start:end].split("\n"))
    return [line for line in lines if line]


def verdict_failed(diff, expected):
    return diff != expected


def is_absent(path, impl, name):
    return impl is not None and (path, impl[0], name) in ABSENT


def expected_diff(path, impl, name):
    """The reviewed diff of an item: under (first impl string, name), or under (path, name)."""
    if impl is not None and (impl[0], name) in EXPECTED:
        return EXPECTED[(impl[0], name)]
    return EXPECTED.get((path, name), [])


def compare(copy_dir, other_dir, items, mutate=None):
    """Print the comparison and return the number of failures. `mutate` is an index into
    `items`; that item of OTHER_DIR gets one extra line, in memory."""
    failures = 0
    for idx, (path, impl, kind, name) in enumerate(items):
        scope = " ".join(impl).removeprefix("impl ").removesuffix(" {") if impl else ""
        label = f"{path} :: {scope + ' :: ' if scope else ''}{kind} {name}"
        try:
            texts = []
            for d, other in ((copy_dir, False), (other_dir, True)):
                src = open(f"{d}/{MOVED.get(path, path) if other else path}",
                           encoding="utf-8").read()
                code, shape = lex(src)
                if other and is_absent(path, impl, name):
                    try:
                        locate(shape, impl, kind, name)
                    except Missing:
                        break
                    raise Missing("listed in ABSENT, but 5.0.0 has it")
                start, end = locate(shape, impl, kind, name)
                if other and mutate == idx:
                    # Before the closing `}` or `;`, so that the change is inside the item.
                    src = src[:end - 1] + "\nmutation()\n" + src[end - 1:]
                    code, shape = lex(src)
                    start, end = locate(shape, impl, kind, name)
                texts.append(normalized(code, start, end))
            if len(texts) < 2:
                if mutate is None:
                    COUNT["absent"] += 1
                    print(f"-- {label}: absent in 5.0.0 (reviewed)")
                continue
        except (Missing, OSError, ValueError) as e:
            print(f"?? {label}: {e}")
            failures += 1
            continue
        diff = list(difflib.unified_diff(texts[0], texts[1], lineterm="", n=0))[2:]
        expected = expected_diff(path, impl, name)
        status = "==" if not diff else "!="
        if mutate is None and not verdict_failed(diff, expected):
            COUNT["identical" if not diff else "changed"] += 1
        verdict = "" if diff == expected else "  UNEXPECTED"
        if mutate is None or verdict:
            print(f"{status} {label}{verdict}")
            for line in diff:
                print("     " + line)
        if verdict:
            failures += 1
    return failures


def self_test(pairs):
    """Each change to an item of an OTHER tree must make the comparison fail."""
    missed, total = [], 0
    for copy_dir, other_dir, items in pairs:
        for idx, (path, impl, kind, name) in enumerate(items):
            if is_absent(path, impl, name):
                total -= 1
                continue
            print(f"-- self-test: change {kind} {name} in {path}")
            if compare(copy_dir, other_dir, items, mutate=idx) == 0:
                missed.append(name)
        total += len(items)
    if missed:
        print(f"self-test FAILED: changes to {missed} were not reported")
        return 1
    print(f"self-test: all {total} changes were reported")
    return 0


def main(argv):
    test = "--self-test" in argv
    args = [a for a in argv if a != "--self-test"]
    if len(args) != 4:
        sys.exit(__doc__)
    pairs = [(args[0], args[1], ITEMS), (args[2], args[3], X_ITEMS)]
    failures = sum(compare(*pair) for pair in pairs)
    print(f"{len(ITEMS) + len(X_ITEMS)} items: {COUNT['identical']} identical, "
          f"{COUNT['changed']} changed as reviewed, {COUNT['absent']} absent in 5.0.0, "
          f"{failures} failures")
    if failures:
        return 1
    return self_test(pairs) if test else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
