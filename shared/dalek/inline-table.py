#!/usr/bin/env python3
"""Hand edit of the Aeneas output, applied by extract.sh after the patches.

Aeneas writes the basepoint table ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN as one monadic
definition: 768 binds `let feN <- FieldElement51.from_limbs (Array.make 5#usize [...])`, then
`ok` of a 32 x 8 array of AffineNielsPoint records. The script replaces the body with one
`ok` of the literal, where each `feN` is its array. The two bodies are equal, because
`from_limbs` is `ok limbs`. The kernel does not reduce `bind` of `Result`, so a proof can
read the table only after this edit.

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


def main(path):
    src = open(path).read()
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
    final = re.sub(r"\b(fe\d*)\b", lambda m: "(" + arrays[m.group(1)] + ")", final)
    head = HEAD.replace(":= do\n", ":=\n")
    open(path, "w").write(src[:i] + head + final + src[end:])


if __name__ == "__main__":
    main(sys.argv[1])
