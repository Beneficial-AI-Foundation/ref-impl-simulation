#!/usr/bin/env python3
"""Hand edit of the Aeneas output, applied by extract.sh after the patches.

Aeneas writes the basepoint table ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN as one monadic
definition: 768 binds `let feN <- FieldElement51.from_limbs (Array.make 5#usize [...])`, then
`ok` of a 32 x 8 array of AffineNielsPoint records. The script replaces the body with one
`ok` of the literal, where each `feN` is its array. The two bodies are equal, because
`from_limbs` is `ok limbs`. The script stops if `from_limbs` has another body, up to the next docstring.
`Result.bind` is a `partial_fixpoint`, so `bind (ok x) f` is equal to `f x` only by the
theorem `bind_ok`, not by reduction. The edit lets `decide +kernel` read the table. A proof
by `bind_ok` does not need it, but `simp` on the 768 binds exceeds the default limits.
Lean does not check that the two bodies are equal, so this edit is in the trusted base.

Usage: inline-table.py <Funs.lean>. The script edits the file in place. It stops with an
error if the file does not have the expected shape.
"""
import re
import sys

NAME = "backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"
HEAD = f"def {NAME}\n  : Result edwards.EdwardsBasepointTable := do\n"
BIND = re.compile(
    r"  let (fe\d*) ←\s*backend\.serial\.u64\.field\.FieldElement51\.from_limbs\s*"
    r"\((Array\.make 5#usize \[[^\]]*\])\)\n")
FINAL = "  ok\n    (Array.make 32#usize"
FROM_LIMBS = (
    "def backend.serial.u64.field.FieldElement51.from_limbs\n"
    "  (limbs : Array Std.U64 5#usize) :\n"
    "  Result backend.serial.u64.field.FieldElement51\n"
    "  := do\n"
    "  ok limbs\n\n/--")


def main(path):
    src = open(path).read()
    if src.count(FROM_LIMBS) != 1:
        sys.exit("inline-table.py: the body of from_limbs is not `ok limbs`")
    i = src.index(HEAD)
    start = i + len(HEAD)
    end = src.index("\n/--", start)
    body = src[start:end]
    k = body.index(FINAL)
    binds, final = body[:k], body[k:]
    arrays = {}
    pos = 0
    for m in BIND.finditer(binds):
        if m.start() != pos:
            sys.exit(f"inline-table.py: unexpected text before {m.group(1)}")
        pos = m.end()
        arrays[m.group(1)] = re.sub(r"\s+", " ", m.group(2)).replace("[ ", "[").replace(" ]", "]")
    if pos != len(binds) or len(arrays) != 768:
        sys.exit(f"inline-table.py: expected 768 binds of from_limbs, found {len(arrays)}")
    if re.search(r"^\S", final[len(FINAL):], re.M):
        sys.exit("inline-table.py: unexpected text after the table")
    used = []
    final = re.sub(r"\b(fe\d*)\b",
                   lambda m: used.append(m.group(1)) or "(" + arrays[m.group(1)] + ")", final)
    if sorted(used) != sorted(arrays):
        sys.exit("inline-table.py: the table does not use each bind exactly once")
    head = HEAD.replace(":= do\n", ":=\n")
    open(path, "w").write(src[:i] + head + final + src[end:])


if __name__ == "__main__":
    main(sys.argv[1])
