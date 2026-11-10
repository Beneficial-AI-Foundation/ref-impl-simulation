-- [x25519_dalek]: external functions.
-- Charon leaves the calls of x25519-dalek into curve25519-dalek and zeroize opaque, and Aeneas
-- declares them as axioms in `x25519/FunsExternal_Template.lean`. This file defines each of
-- them as the function of the same Rust name in the fork's translation (`Curve25519Dalek.Funs`)
-- or in the fork's model of `zeroize` (`Zeroize/Contract.lean`). It adds no axiom.
--
-- Three kinds of definitions:
-- 1. The same function: `mul_clamped`, `to_bytes`, `as_bytes`, `ct_eq`, `eq`, `identity` and
--    `zeroize` of `MontgomeryPoint`.
-- 2. The same function, with the trait arguments repacked: `is_identity` and the two `zeroize`
--    impls of the `zeroize` crate. Aeneas declares the trait structures of `subtle`,
--    `curve25519_dalek::traits` and `zeroize` again in `X25519Dalek/Types.lean`, in the namespace
--    `x25519_dalek`. Each definition copies the fields into the fork's structure of the same
--    trait and calls the fork's function.
-- 3. The dispatch on the build: `EdwardsPoint::mul_base_clamped` and
--    `EdwardsPoint::to_montgomery`. The fork has one function per build. `mul_base_clamped`
--    dispatches on `get_target`, as the fork's translation does for the functions whose body
--    differs by build (for example `MontgomeryPoint::mul_base`), and `to_montgomery` calls the
--    function of the point's build.
module
public import Aeneas
public import X25519Dalek.Types
public import Curve25519Dalek.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

noncomputable section

/-! ## 1. The same function -/

/-- [curve25519_dalek::montgomery::{impl subtle::ConstantTimeEq for MontgomeryPoint}::ct_eq] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint →
      x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint → Result subtle.Choice :=
  Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq

/-- [curve25519_dalek::montgomery::{impl core::cmp::PartialEq for MontgomeryPoint}::eq] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint →
      x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint → Result Bool :=
  Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq

/-- [curve25519_dalek::montgomery::{impl curve25519_dalek::traits::Identity for
MontgomeryPoint}::identity] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity :
    Result x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint :=
  Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity

/-- [curve25519_dalek::montgomery::{impl zeroize::Zeroize for MontgomeryPoint}::zeroize] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint →
      Result x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint :=
  Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize

/-- [curve25519_dalek::montgomery::{MontgomeryPoint}::mul_clamped] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint → Array Std.U8 32#usize →
      Result x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint :=
  Curve25519Dalek.montgomery.MontgomeryPoint.mul_clamped

/-- [curve25519_dalek::montgomery::{MontgomeryPoint}::as_bytes] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.as_bytes :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint → Result (Array Std.U8 32#usize) :=
  Curve25519Dalek.montgomery.MontgomeryPoint.as_bytes

/-- [curve25519_dalek::montgomery::{MontgomeryPoint}::to_bytes] -/
@[reducible]
def curve25519_dalek.montgomery.MontgomeryPoint.to_bytes :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint → Result (Array Std.U8 32#usize) :=
  Curve25519Dalek.montgomery.MontgomeryPoint.to_bytes

/-! ## 2. The same function, with the trait arguments repacked -/

/-- [curve25519_dalek::traits::{impl curve25519_dalek::traits::IsIdentity for T}::is_identity] -/
@[reducible]
def curve25519_dalek.traits.IsIdentity.Blanket.is_identity {T : Type}
    (subtleConstantTimeEqInst : x25519_dalek.subtle.ConstantTimeEq T)
    (IdentityInst : x25519_dalek.curve25519_dalek.traits.Identity T) : T → Result Bool :=
  Curve25519Dalek.traits.IsIdentity.Blanket.is_identity
    { ct_eq := subtleConstantTimeEqInst.ct_eq } { identity := IdentityInst.identity }

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]. `Funs.lean` uses this name inside
`namespace x25519_dalek`, so Lean resolves it to this definition, not to the fork's
`_root_.zeroize.Zeroize.Blanket.zeroize`. -/
@[reducible]
def x25519_dalek.zeroize.Zeroize.Blanket.zeroize {Z : Type}
    (DefaultIsZeroesInst : x25519_dalek.zeroize.DefaultIsZeroes Z) : Z → Result Z :=
  _root_.zeroize.Zeroize.Blanket.zeroize
    { coremarkerCopyInst := DefaultIsZeroesInst.coremarkerCopyInst
      coredefaultDefaultInst := DefaultIsZeroesInst.coredefaultDefaultInst }

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]. `Funs.lean` uses this name inside
`namespace x25519_dalek`, so Lean resolves it to this definition, not to the fork's
`_root_.Array.Insts.ZeroizeZeroize.zeroize`. -/
@[reducible]
def x25519_dalek.Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Std.Usize}
    (ZeroizeInst : x25519_dalek.zeroize.Zeroize Z) : Array Z N → Result (Array Z N) :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize { zeroize := ZeroizeInst.zeroize }

/-! ## 3. The dispatch on the build -/

/-- [curve25519_dalek::edwards::{EdwardsPoint}::mul_base_clamped]: the function of the build
that `get_target` names. -/
def curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped
    (bytes : Array Std.U8 32#usize) : Result curve25519_dalek.edwards.EdwardsPoint := do
  let tgt ← get_target
  if tgt = "x86_64-tables"
  then do
    let p ← Curve25519Dalek.edwards.«EdwardsPointx86_64-tables».mul_base_clamped bytes
    ok (.«x86_64-tables» p)
  else
    if tgt = "x86_64-no-tables"
    then do
      let p ← Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables».mul_base_clamped bytes
      ok (.«x86_64-no-tables» p)
    else
      if tgt = "i686-tables"
      then do
        let p ← Curve25519Dalek.edwards.«EdwardsPointi686-tables».mul_base_clamped bytes
        ok (.«i686-tables» p)
      else do
        let p ← Curve25519Dalek.edwards.«EdwardsPointi686-no-tables».mul_base_clamped bytes
        ok (.«i686-no-tables» p)

/-- [curve25519_dalek::edwards::{EdwardsPoint}::to_montgomery]: the function of the point's
build. -/
def curve25519_dalek.edwards.EdwardsPoint.to_montgomery :
    curve25519_dalek.edwards.EdwardsPoint →
      Result x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint
  | .«x86_64-tables» p => Curve25519Dalek.edwards.«EdwardsPointx86_64-tables».to_montgomery p
  | .«x86_64-no-tables» p =>
    Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables».to_montgomery p
  | .«i686-tables» p => Curve25519Dalek.edwards.«EdwardsPointi686-tables».to_montgomery p
  | .«i686-no-tables» p => Curve25519Dalek.edwards.«EdwardsPointi686-no-tables».to_montgomery p
