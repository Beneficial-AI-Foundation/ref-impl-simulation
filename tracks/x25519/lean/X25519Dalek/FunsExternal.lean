-- [x25519_dalek]: external functions.
-- Charon leaves the three curve25519-dalek functions that the entry points call opaque, and Aeneas
-- declares them as axioms in `FunsExternal_Template.lean`. This file replaces the axioms with
-- the Aeneas translations of the same functions in `Curve25519Dalek.Funs`, which have the
-- same names:
--   `curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped`
--   `curve25519_dalek.montgomery.MontgomeryPoint.to_bytes`
--   `curve25519_dalek.montgomery.MontgomeryPoint.as_bytes`
module
public import Aeneas
public import X25519Dalek.Types
public import Curve25519Dalek.Funs
