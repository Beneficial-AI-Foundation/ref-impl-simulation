#!/usr/bin/env python3
"""Check that the proved trees agree with the libsignal versions on the paths of the theorems.

Usage: compare-dalek5.py [--self-test] COPY_DIR OTHER_DIR X_COPY_DIR X_OTHER_DIR

COPY_DIR is the curve25519-dalek copy that this track extracts (`real-dalek/curve25519-dalek`).
OTHER_DIR is curve25519-dalek 5.0.0, the version that libsignal uses. X_COPY_DIR is the
x25519-dalek copy that this track extracts (`real-x25519/x25519-dalek`, version 2.0.1).
X_OTHER_DIR is x25519-dalek 3.0.0, the version that libsignal uses. For each item in `ITEMS`
and `X_ITEMS`, the script extracts its text from both trees, removes comments and blank
lines, and compares the results. An item is a function or a constant, found by its `impl`
block and its name.

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
]

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
}


class Missing(Exception):
    pass


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
    """End of the item that starts at `start`: its body for a function or macro, its `;`
    for a constant. Brackets in the signature, such as `[u8; 32]`, are skipped."""
    depth, j = 0, start
    while True:
        c = shape[j]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif depth == 0 and c == "{" and kind != "const":
            return close(shape, j)
        elif depth == 0 and c == ";" and kind == "const":
            return j + 1
        elif depth == 0 and c == "{":
            j = close(shape, j) - 1
        j += 1


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
    elif kind == "const":
        pattern = rf"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+{name}\b"
    else:
        pattern = rf"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?fn\s+{name}\b"
    if impl is None:
        pattern = pattern.replace(r"^\s*", "^")
    hits = [lo + m.start() for lo, hi in scopes
            for m in re.finditer(pattern, shape[lo:hi], re.M)]
    if len(hits) != 1:
        raise Missing(f"{kind} {name}: {len(hits)} matches")
    return hits[0], item_end(shape, hits[0], kind)


def normalized(code, start, end):
    lines = (line.strip() for line in code[start:end].split("\n"))
    return [line for line in lines if line]


def key(path, impl, name):
    if impl is not None and impl[0].startswith("Mul<&Scalar>"):
        return (impl[0], name)
    return (path, name)


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
                src = open(f"{d}/{path}", encoding="utf-8").read()
                code, shape = lex(src)
                start, end = locate(shape, impl, kind, name)
                if other and mutate == idx:
                    # Before the closing `}` or `;`, so that the change is inside the item.
                    src = src[:end - 1] + "\nmutation()\n" + src[end - 1:]
                    code, shape = lex(src)
                    start, end = locate(shape, impl, kind, name)
                texts.append(normalized(code, start, end))
        except (Missing, OSError, ValueError) as e:
            print(f"?? {label}: {e}")
            failures += 1
            continue
        diff = list(difflib.unified_diff(texts[0], texts[1], lineterm="", n=0))[2:]
        expected = EXPECTED.get(key(path, impl, name), [])
        status = "==" if not diff else "!="
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
    print(f"{len(ITEMS) + len(X_ITEMS)} items, {failures} failures")
    if failures:
        return 1
    return self_test(pairs) if test else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
