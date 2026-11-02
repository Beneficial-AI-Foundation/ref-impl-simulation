import Lake
open Lake DSL

require aeneas from "aeneas-backend"
require PrimeCert from "primecert"

package ristrettosim where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- Reference: Aeneas output of `ref-plain` plus the hand-written ZMod p field model. -/
@[default_target] lean_lib RistrettoRef where
  globs := #[.submodules `RistrettoRef]

/-- Real: Aeneas output of curve25519-dalek (Ristretto `decompress` and `compress`) plus
support files copied from track B. -/
@[default_target] lean_lib Curve25519Dalek where
  globs := #[.one `Curve25519Dalek.Types, .one `Curve25519Dalek.TypesExternal,
    .one `Curve25519Dalek.Funs, .one `Curve25519Dalek.FunsExternal,
    .one `Curve25519Dalek.Math.Basic, .one `Curve25519Dalek.Math.PrimeCerts,
    .one `Curve25519Dalek.Auxiliary]

/-- Field specs ported by track B from curve25519-dalek-lean-verify, copied unchanged. -/
@[default_target] lean_lib DalekPort where
  globs := #[.submodules `Curve25519Dalek.Specs]

@[default_target] lean_lib Sim where
  globs := #[.submodules `Sim]
