-- [x25519_dalek]: external types.
-- Charon leaves the two types below opaque, and Aeneas declares them as axioms in
-- `TypesExternal_Template.lean`. This file replaces the axioms with the definitions of the
-- shared library, which have the same names:
--   `curve25519_dalek.backend.serial.u64.field.FieldElement51`, in `Curve25519Dalek.Types`
--   `subtle.Choice`, in `Curve25519Dalek.TypesExternal`
module
public import Aeneas
public import Curve25519Dalek.Types
