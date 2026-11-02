#!/usr/bin/env python3
"""Check that two curve25519-dalek trees agree on the path of `decompress_refines`.

Usage: compare-dalek5.py [--self-test] COPY_DIR OTHER_DIR

COPY_DIR is the copy that this track extracts (`../x25519/real-dalek/curve25519-dalek`). OTHER_DIR is
curve25519-dalek 5.0.0, the version that libsignal uses. For each item in `ITEMS`, the
script extracts its text from both trees, removes comments and blank lines, and compares
the results. An item is a function or a constant, found by its `impl` block and its name.

The script prints `==` for an identical item and `!=` with the diff otherwise. It exits 1
if an item is missing or ambiguous in either tree, or if a diff differs from the reviewed
diff in `EXPECTED`. With `--self-test`, it also changes each item of OTHER_DIR in memory
and checks that the comparison reports the change.
"""

import difflib
import re
import sys

FIELD = "src/backend/serial/u64/field.rs"

# (file, block, kind, name). The block is a list of substrings that must all occur in the
# header line of an `impl` or `mod` block, or None for an item outside any block.
RIST = "src/ristretto.rs"
FE = "src/field.rs"

ITEMS = [
    (FIELD, ["AddAssign<", "for FieldElement51"], "fn", "add_assign"),
    (FIELD, ["Add<", "for &FieldElement51"], "fn", "add"),
    (FIELD, ["Sub<", "for &FieldElement51"], "fn", "sub"),
    (FIELD, ["Mul<", "for &FieldElement51"], "fn", "mul"),
    (FIELD, ["Neg for &FieldElement51"], "fn", "neg"),
    (FIELD, ["ConditionallySelectable for FieldElement51"], "fn", "conditional_assign"),
    (FIELD, ["impl FieldElement51 {"], "fn", "from_limbs"),
    (FIELD, ["impl FieldElement51 {"], "const", "ONE"),
    (FIELD, ["impl FieldElement51 {"], "fn", "negate"),
    (FIELD, ["impl FieldElement51 {"], "fn", "reduce"),
    (FIELD, ["impl FieldElement51 {"], "fn", "from_bytes"),
    (FIELD, ["impl FieldElement51 {"], "fn", "to_bytes"),
    (FIELD, ["impl FieldElement51 {"], "fn", "pow2k"),
    (FIELD, ["impl FieldElement51 {"], "fn", "square"),
    ("src/backend/serial/u64/constants.rs", None, "const", "EDWARDS_D"),
    ("src/backend/serial/u64/constants.rs", None, "const", "SQRT_M1"),
    ("src/backend/serial/u64/constants.rs", None, "const", "INVSQRT_A_MINUS_D"),
    (FE, ["ConstantTimeEq for FieldElement"], "fn", "ct_eq"),
    (FE, ["impl FieldElement {"], "fn", "is_negative"),
    (FE, ["impl FieldElement {"], "fn", "is_zero"),
    (FE, ["impl FieldElement {"], "fn", "pow22501"),
    (FE, ["impl FieldElement {"], "fn", "pow_p58"),
    (FE, ["impl FieldElement {"], "fn", "sqrt_ratio_i"),
    (FE, ["impl FieldElement {"], "fn", "invsqrt"),
    (RIST, ["impl CompressedRistretto {"], "fn", "as_bytes"),
    (RIST, ["impl CompressedRistretto {"], "fn", "decompress"),
    (RIST, ["mod decompress"], "fn", "step_1"),
    (RIST, ["mod decompress"], "fn", "step_2"),
]

# The reviewed diffs, as printed by this script: the extraction edits of
# `curve25519-dalek-lean-verify` and one change of visibility (`pow_p58`). Any other difference
# fails the check.
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
    (FE, "pow_p58"): [
        "@@ -1 +1 @@",
        "-fn pow_p58(&self) -> FieldElement {",
        "+pub(crate) fn pow_p58(&self) -> FieldElement {",
    ],
    (FE, "sqrt_ratio_i"): [
        "@@ -13,2 +13 @@",
        "-let r_neg = -&r;",
        "-r.conditional_assign(&r_neg, r_is_negative);",
        "+r.conditional_negate(r_is_negative);",
    ],
    (RIST, "step_2"): [
        "@@ -7,6 +7,2 @@",
        "-let neg_d = -&constants::EDWARDS_D;",
        "-let u1_sq = u1.square();",
        "-let neg_d_u1_sq = &neg_d * &u1_sq;",
        "-let v = &neg_d_u1_sq - &u2_sqr;",
        "-let v_u2_sqr = &v * &u2_sqr;",
        "-let (ok, I) = v_u2_sqr.invsqrt();",
        "+let v = &(&(-&constants::EDWARDS_D) * &u1.square()) - &u2_sqr;",
        "+let (ok, I) = (&v * &u2_sqr).invsqrt();",
        "@@ -14,4 +10,2 @@",
        "-let Dx_v = &Dx * &v;",
        "-let Dy = &I * &Dx_v;",
        "-let s_plus_s = &s + &s;",
        "-let mut x = &s_plus_s * &Dx;",
        "+let Dy = &I * &(&Dx * &v);",
        "+let mut x = &(&s + &s) * &Dx;",
        "@@ -19,2 +13 @@",
        "-let x_negated = -&x;",
        "-x.conditional_assign(&x_negated, x_neg);",
        "+x.conditional_negate(x_neg);",
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
                  for m in re.finditer(r"^(?:impl|mod)\b[^\n]*", shape, re.M)
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
    return (path, name)


def compare(copy_dir, other_dir, mutate=None):
    """Print the comparison and return the number of failures. `mutate` is an index into
    `ITEMS`; that item of OTHER_DIR gets one extra line, in memory."""
    failures = 0
    for idx, (path, impl, kind, name) in enumerate(ITEMS):
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


def self_test(copy_dir, other_dir):
    """Each change to an item of OTHER_DIR must make the comparison fail."""
    missed = []
    for idx, (path, impl, kind, name) in enumerate(ITEMS):
        print(f"-- self-test: change {kind} {name} in {path}")
        if compare(copy_dir, other_dir, mutate=idx) == 0:
            missed.append(name)
    if missed:
        print(f"self-test FAILED: changes to {missed} were not reported")
        return 1
    print(f"self-test: all {len(ITEMS)} changes were reported")
    return 0


def main(argv):
    test = "--self-test" in argv
    args = [a for a in argv if a != "--self-test"]
    if len(args) != 2:
        sys.exit(__doc__)
    failures = compare(*args)
    print(f"{len(ITEMS)} items, {failures} failures")
    if failures:
        return 1
    return self_test(*args) if test else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
