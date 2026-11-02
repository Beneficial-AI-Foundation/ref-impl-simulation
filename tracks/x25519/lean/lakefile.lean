import Lake
open Lake DSL

require aeneas from "aeneas-backend"
require PrimeCert from "primecert"

package x25519sim where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- Reference: Aeneas output of `ref-plain` plus the hand-written ZMod p field model. -/
@[default_target] lean_lib X25519Ref where
  globs := #[.submodules `X25519Ref]

/-- Real: Aeneas output of curve25519-dalek (Montgomery path) plus two support files
copied from curve25519-dalek-lean-verify. -/
@[default_target] lean_lib Curve25519Dalek where
  globs := #[.one `Curve25519Dalek.Types, .one `Curve25519Dalek.TypesExternal,
    .one `Curve25519Dalek.Funs, .one `Curve25519Dalek.FunsExternal,
    .one `Curve25519Dalek.Math.Basic, .one `Curve25519Dalek.Math.PrimeCerts,
    .one `Curve25519Dalek.Auxiliary]

/-- Field specs copied from curve25519-dalek-lean-verify (Aeneas 6e167c9b) and ported to Aeneas
d119a474. `Sim.Discharge` imports them, so the default build builds them. -/
lean_lib DalekPort where
  globs := #[.submodules `Curve25519Dalek.Specs]

@[default_target] lean_lib Sim where
  globs := #[.one `Sim.Pilot, .one `Sim.Discharge, .one `Sim.LadderMath, .one `Sim.RefSide,
    .one `Sim.Bytes, .one `Sim.RealSide, .one `Sim.Full]
