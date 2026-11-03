#!/usr/bin/env python3
"""Compute the polynomial certificates of DalekSim/Edwards.lean with Singular.

Curve: -x^2 + y^2 = 1 + d x^2 y^2 (a = -1). For every identity, Singular's `lift` writes the
polynomial as a combination of the curve equations e1, e2, e3, and this script prints the
cofactors in Lean syntax. The Lean file checks each certificate with `linear_combination`,
so this script is not trusted.

Usage: gen.py SINGULAR_BINARY
The output has one `linear_combination` per target. `closure`, `assoc_x` and `assoc_y` are
the proofs of `closure_core`, `assoc_x_core` and `assoc_y_core` in
shared/dalek/lean/DalekSim/Edwards.lean.

Singular comes from the PyPI package passagemath-singular, for example:
    python3 -m venv ~/.venvs/cas && ~/.venvs/cas/bin/pip install passagemath-singular
    ~/.venvs/cas/bin/python gen.py \
        ~/.venvs/cas/lib/python3.12/site-packages/sage_wheels/bin/Singular
"""
import re
import subprocess
import sys

HEADER = """
ring r=0,(x1,x2,x3,y1,y2,y3,d),dp;
short=0;
poly e1 = -x1^2+y1^2-1-d*x1^2*y1^2;
poly e2 = -x2^2+y2^2-1-d*x2^2*y2^2;
poly e3 = -x3^2+y3^2-1-d*x3^2*y3^2;
ideal I = e1,e2,e3;
poly D12p = 1+d*x1*x2*y1*y2; poly D12m = 1-d*x1*x2*y1*y2;
poly D23p = 1+d*x2*x3*y2*y3; poly D23m = 1-d*x2*x3*y2*y3;
poly N12x = x1*y2+y1*x2; poly N12y = y1*y2+x1*x2;
poly N23x = x2*y3+y2*x3; poly N23y = y2*y3+x2*x3;
"""

# Each target is a polynomial that must lie in the ideal (e1, e2, e3).
TARGETS = {
    # Closure: (N12x / D12p, N12y / D12m) is on the curve, denominators multiplied out.
    "closure": "-N12x^2*D12m^2 + N12y^2*D12p^2 - D12p^2*D12m^2 - d*N12x^2*N12y^2",
    # Associativity, x-coordinate: A * B - C * E.
    "assoc_x": "(N12x*y3*D12m + N12y*x3*D12p)*(D23p*D23m + d*x1*y1*N23x*N23y)"
               " - (x1*N23y*D23p + y1*N23x*D23m)*(D12p*D12m + d*x3*y3*N12x*N12y)",
    # Associativity, y-coordinate: A' * B' - C' * E'.
    "assoc_y": "(N12y*y3*D12p + N12x*x3*D12m)*(D23p*D23m - d*x1*y1*N23x*N23y)"
               " - (y1*N23y*D23p + x1*N23x*D23m)*(D12p*D12m - d*x3*y3*N12x*N12y)",
}


def run(singular):
    script = HEADER
    for name, poly in TARGETS.items():
        script += f'poly T = {poly};\n"BEGIN {name}"; size(T); deg(T);\n'
        script += "matrix L = lift(I, T);\n"
        script += 'print(L[1,1]); "SEP"; print(L[2,1]); "SEP"; print(L[3,1]);\n'
        script += f'"END {name}"; kill T; kill L;\n'
    script += "quit;\n"
    out = subprocess.run([singular, "-q"], input=script, capture_output=True, text=True,
                         check=True).stdout
    return out


def lean(p):
    # Singular prints products with `*` and powers with `^`, as Lean does.
    return re.sub(r"\s+", "", p)


def wrap(line, width=100):
    """Break a long `linear_combination` line before a `+` or `-` sign."""
    out, cur = [], line
    while len(cur) > width:
        cut = max(cur.rfind("+", 0, width), cur.rfind("-", 0, width))
        out.append(cur[:cut].rstrip())
        cur = "    " + cur[cut:]
    out.append(cur)
    return "\n".join(out)


def main():
    out = run(sys.argv[1])
    for name in TARGETS:
        block = out.split(f"BEGIN {name}")[1].split(f"END {name}")[0]
        lines = block.strip().split("\n")
        size, deg = lines[0], lines[1]
        body = "\n".join(lines[2:])
        q = [lean(s) for s in body.split("SEP")]
        print(f"-- {name}: target with {size} terms, degree {deg}; cofactor sizes "
              + ", ".join(str(0 if s == "0" else s.count("+") + s.count("-") + 1) for s in q))
        terms = [f"({c}) * h{i + 1}" for i, c in enumerate(q) if c != "0"]
        print(wrap("  linear_combination " + " + ".join(terms)))
        print()


if __name__ == "__main__":
    main()
