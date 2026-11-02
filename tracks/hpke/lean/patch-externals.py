#!/usr/bin/env python3
"""Turn FunsExternal_Template.lean into FunsExternal.lean.
Replaces selected `axiom` blocks with definitions (shared HKDF model, std models).
All other axioms stay as generated."""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).parent

REF = {
"hacspec_cryptolib.hkdf_extract": '''def hacspec_cryptolib.hkdf_extract
  (ha : hacspec_cryptolib.HashAlgorithm) (k salt : hacspec_lib.Seq Std.U8) :
  Result (core.result.Result (hacspec_lib.Seq Std.U8) Std.U8) :=
  match ha with
  | .SHA256 => ok (.Ok { b := Shared.extract .sha256 salt.b.val k.b.val })
  | _ => ok (.Err Ref.UNSUPPORTED_ALGORITHM)''',
"hacspec_cryptolib.hkdf_expand": '''def hacspec_cryptolib.hkdf_expand
  (ha : hacspec_cryptolib.HashAlgorithm) (k info : hacspec_lib.Seq Std.U8) (len : Std.Usize) :
  Result (core.result.Result (hacspec_lib.Seq Std.U8) Std.U8) :=
  match ha with
  | .SHA256 =>
    ok (match Shared.expand .sha256 k.b.val info.b.val len.val with
        | some v => .Ok { b := v }
        | none => .Err Ref.HKDF_ERROR)
  | _ => ok (.Err Ref.UNSUPPORTED_ALGORITHM)''',
}
REF_PRE = '''
/-- Error codes of `hacspec_cryptolib` (`hpke-spec/hacspec_cryptolib/src/cryptolib.rs`). -/
def Ref.HKDF_ERROR : Std.U8 := 2#u8
def Ref.UNSUPPORTED_ALGORITHM : Std.U8 := 6#u8

/-- The reference hash enum mapped to the shared model. As in the original
`hacspec_cryptolib`, the HKDF functions support SHA-256 only and return
`UNSUPPORTED_ALGORITHM` for SHA-384 and SHA-512. -/
def Ref.hashOf : hacspec_cryptolib.HashAlgorithm → Shared.Hash
  | .SHA256 => .sha256
  | .SHA384 => .sha384
  | .SHA512 => .sha512
'''

REAL = {
"Shared0T.Insts.CoreBorrowBorrow.borrow": '''def Shared0T.Insts.CoreBorrowBorrow.borrow {T : Type} (x : T) : Result T := ok x''',
"core.hint.must_use": '''def core.hint.must_use {T : Type} (x : T) : Result T := ok x''',
"alloc.fmt.format": '''def alloc.fmt.format (_ : core.fmt.Arguments) : Result String := ok Real.fmtString''',
"core.str.Str.as_bytes": '''def core.str.Str.as_bytes (s : Str) : Result (Slice Std.U8) := ok s''',
"alloc.slice.Slice.join": '''def alloc.slice.Slice.join
  {T : Type} {Separator : Type} {Clause0_Output : Type}
  (inst : alloc.slice.Join (Slice T) Separator Clause0_Output)
  (v : Slice T) (sep : Separator) : Result Clause0_Output :=
  inst.join v sep''',
"Slice.Insts.AllocSliceJoinShared0SliceVec.join": '''def Slice.Insts.AllocSliceJoinShared0SliceVec.join
  {T : Type} {V : Type} (cl : core.clone.Clone T)
  (bor : core.borrow.Borrow V (Slice T)) (vs : Slice V) (sep : Slice T) :
  Result (alloc.vec.Vec T) := do
  let parts ← List.mapM bor.borrow vs.val
  let flat := List.intercalate sep.val (parts.map (·.val))
  let flat' ← List.clone cl.clone flat
  Real.vecOfList flat'.val''',
}

def patch(tmpl, out, table, pre="", extra_imports=()):
    s = (ROOT / tmpl).read_text()
    for name, d in table.items():
        pat = re.compile(r'axiom ' + re.escape(name) + r'\b[\s\S]*?(?=\n\n|\Z)')
        s, n = pat.subn(lambda m: d, s, count=1)
        if n != 1:
            sys.exit(f"{tmpl}: axiom {name} not found")
    for imp in extra_imports:
        s = s.replace("public import Aeneas\n", f"public import Aeneas\npublic import {imp}\n", 1)
    if pre:
        s = re.sub(r'(\nopen (Ref|Real)\n)', lambda m: m.group(1) + pre, s, count=1)
    (ROOT / out).write_text(s)

patch("Ref/FunsExternal_Template.lean", "Ref/FunsExternal.lean", REF, REF_PRE, ["Shared.Hkdf"])
REAL_PRE = '''
/-- Aeneas models `core::fmt::Arguments` as `Unit`, so `format!` output carries no information.
We model it as total, returning one unspecified string. -/
opaque Real.fmtString : String
/-- A list as a `Vec`. It panics if the length exceeds `Usize.max`. -/
def Real.vecOfList {T : Type} (l : List T) : Result (alloc.vec.Vec T) :=
  if h : l.length ≤ Usize.max then ok (alloc.vec.Vec.from l h) else fail .panic
'''
patch("Real/FunsExternal_Template.lean", "Real/FunsExternal.lean", REAL, REAL_PRE)
import shutil
shutil.copy(ROOT / "Real/TypesExternal_Template.lean", ROOT / "Real/TypesExternal.lean")
