#!/usr/bin/env python3
"""Find bare names in Aeneas Lean output that Lean binds to the wrong declaration.

Aeneas writes references to items of the local crate relative to the crate namespace
(Aeneas issue #1458). Lean elaborates the body of `def P.x` with the namespaces of `P`
open, so a reference `t` binds to `NS.Q.t` when that exists for a non-empty prefix `Q`
of `P`, and not to the intended `NS.t`. If the binding is the definition itself and the
call is structural recursion, Lean accepts a definition that differs from the Rust code.

Usage: check-short-names.py FILE.lean [FILE.lean ...]

All files must belong to one extraction (one namespace). The script prints one line per
suspicious reference and exits 1 if it finds any.
"""

import re
import sys

KINDS = r"(def|abbrev|theorem|lemma|opaque|axiom|structure|inductive|instance|class|impl_def)"
PREFIX = r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
NAME = r"([A-Za-z_«][\w'.«»]*)"
DECL = re.compile(PREFIX + KINDS + r"\s+" + NAME)
# Aeneas writes long names on the line after the keyword: `def` alone, then `  name`.
# Blank and comment lines may come between the two. Any other line is an error.
DECL_KW = re.compile(PREFIX + KINDS + r"\s*$")
DECL_NAME = re.compile(r"^\s+" + NAME)
ATTR_ONLY = re.compile(r"^@\[[^\]]*\]\s*$")
CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][\w']*)")
FIELD = re.compile(r"^\s+([A-Za-z_][\w']*)\s*:")
IDENT = re.compile(r"(?<![\w'.])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)")
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
COMMENT = re.compile(r"--.*$")


def read_decls(paths):
    """Return the namespace and a list of (file, line, kind, name, body lines)."""
    ns = None
    decls = []
    for path in paths:
        cur = None
        in_ns = False
        pending = None  # kind of a keyword whose name is on the next line
        for lineno, raw in enumerate(open(path, encoding="utf-8"), 1):
            line = raw.rstrip("\n")
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                if ns is None:
                    ns = m.group(1)
                elif ns != m.group(1):
                    sys.exit(f"{path}: namespace {m.group(1)}, expected {ns}")
                in_ns = True
                continue
            if re.match(r"^end\s+", line):
                in_ns = False
                cur = None
                continue
            if not in_ns:
                continue
            if pending is not None:
                if not line.strip() or line.lstrip().startswith("--"):
                    continue
                m = DECL_NAME.match(line)
                if not m:
                    sys.exit(f"{path}:{lineno}: cannot read the name of a `{pending}` declaration")
                cur = [path, lineno, pending, m.group(1), [line[m.end():]]]
                decls.append(cur)
                pending = None
                continue
            m = DECL_KW.match(line)
            if m:
                pending = m.group(1)
                cur = None
                continue
            m = DECL.match(line)
            if m:
                cur = [path, lineno, m.group(1), m.group(2), [line[m.end():]]]
                decls.append(cur)
            elif cur is not None and not ATTR_ONLY.match(line):
                if line and not line[0].isspace() and not line.startswith("|"):
                    cur = None
                else:
                    cur[4].append(line)
    return ns, decls


def declared_names(decls):
    names = set()
    for _, _, kind, name, body in decls:
        names.add(name)
        if kind in ("inductive", "structure", "class"):
            names.add(name + ".mk")
            for line in body:
                m = CTOR.match(line) or (FIELD.match(line) if kind != "inductive" else None)
                if m:
                    names.add(name + "." + m.group(1))
    return names


BINDER = re.compile(r"[({\[]\s*([A-Za-z_][\w' ]*?)\s*:(?!=)")
LET = re.compile(r"\blet\s+([A-Za-z_][\w']*)")
LET_TUPLE = re.compile(r"\blet\s+[(⟨]([^)⟩]*)[)⟩]")
FUN = re.compile(r"\bfun\s+([^=]*?)=>")
PATTERN = re.compile(r"^\s*\|\s*(.*?)=>")
BARE = re.compile(r"(?<![\w'.])([A-Za-z_][\w']*)(?![\w'.])")


def clean(line):
    return COMMENT.sub("", STRING.sub('""', line))


def local_names(body):
    """Names that a definition binds locally. Lean resolves these before any namespace."""
    names = set()
    for line in map(clean, body):
        for rx in (BINDER, LET, LET_TUPLE, FUN, PATTERN):
            for m in rx.finditer(line):
                names.update(BARE.findall(m.group(1)))
    return names


def body_tokens(body):
    for i, line in enumerate(body):
        line = clean(line)
        for m in IDENT.finditer(line):
            # A label in a structure literal (`{ f := v }`) names a field, not a declaration.
            if re.match(r"\s*:=", line[m.end():]):
                continue
            yield i, m.group(1)


def main(paths):
    ns, decls = read_decls(paths)
    if ns is None:
        sys.exit("no namespace found")
    names = declared_names(decls)
    hits = 0
    for path, lineno, kind, name, body in decls:
        if kind not in ("def", "abbrev", "instance", "impl_def"):
            continue
        parts = name.split(".")
        prefixes = [".".join(parts[:k]) for k in range(len(parts) - 1, 0, -1)]
        local = local_names(body)
        for i, tok in body_tokens(body):
            if tok.split(".")[0] in local:
                continue
            bound = next((q + "." + tok for q in prefixes if q + "." + tok in names), None)
            if bound is None or bound == tok:
                continue
            intended = tok if tok in names else None
            what = "self-reference" if bound == name else "binds to " + ns + "." + bound
            note = f"intended {ns}.{intended}" if intended else "no crate-level item of that name"
            print(f"{path}:{lineno + i}: in {ns}.{name}: `{tok}` {what} ({note})")
            hits += 1
    print(f"{len(decls)} declarations, {hits} suspicious references", file=sys.stderr)
    return 1 if hits else 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1:]))
