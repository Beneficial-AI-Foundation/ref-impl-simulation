-- [x25519_dalek]: external types.
-- Charon leaves the two types below opaque, and Aeneas declares them as axioms in
-- `x25519/TypesExternal_Template.lean`. This file defines them with the types of the fork's
-- translation of curve25519-dalek:
--   `subtle.Choice`: the fork's `subtle.Choice` (`Subtle/Types.lean` in the fork), the same
--     name, so this file only imports it.
--   `curve25519_dalek.edwards.EdwardsPoint`: the fork translates four builds, and the fields of
--     `EdwardsPoint` differ between the 64-bit and the 32-bit builds. So the fork has one
--     structure per build, `Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»` and three
--     others. A value of the type below is the point of one build.
module
public import Aeneas
public import Curve25519Dalek.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/-- [curve25519_dalek::edwards::EdwardsPoint]: the point of one of the fork's four builds. -/
inductive curve25519_dalek.edwards.EdwardsPoint where
  | «x86_64-tables» (p : Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»)
  | «x86_64-no-tables» (p : Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables»)
  | «i686-tables» (p : Curve25519Dalek.edwards.EdwardsPoint.«i686-tables»)
  | «i686-no-tables» (p : Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables»)
