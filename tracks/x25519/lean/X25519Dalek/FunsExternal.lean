-- [x25519_dalek]: external functions.
-- Charon leaves the curve25519-dalek and subtle functions that the entry points call opaque,
-- and Aeneas declares them as axioms in `FunsExternal_Template.lean`. This file replaces the
-- axioms with the definitions of the same names in `Curve25519Dalek.Funs` (Aeneas
-- translations) and `Curve25519Dalek.FunsExternal` (the hand definition of `subtle`):
--   `curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped`
--   `curve25519_dalek.montgomery.MontgomeryPoint.to_bytes`
--   `curve25519_dalek.montgomery.MontgomeryPoint.as_bytes`
--   `curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes`
--   `curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq`
--   `Bool.Insts.CoreConvertFromChoice.from`
-- The template also declares the `Drop` impl of `EphemeralSecret`, which the extraction
-- keeps opaque. No definition here calls it, so this file does not define it.
module
public import Aeneas
public import X25519Dalek.Types
public import Curve25519Dalek.Funs
