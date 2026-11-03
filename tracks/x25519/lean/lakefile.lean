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

/-- Real: Aeneas output of x25519-dalek's `x25519`. Its two external functions are the
definitions in `Curve25519Dalek.Funs`. -/
@[default_target] lean_lib X25519Dalek where
  globs := #[.submodules `X25519Dalek]

/-- Field specs copied from curve25519-dalek-lean-verify (Aeneas 6e167c9b) and ported to Aeneas
d119a474. `Sim.Discharge` imports them, so the default build builds them. -/
lean_lib DalekPort where
  globs := #[.submodules `Curve25519Dalek.Specs]

@[default_target] lean_lib Sim where
  globs := #[.one `Sim.Pilot, .one `Sim.Discharge, .one `Sim.LadderMath, .one `Sim.RefSide,
    .one `Sim.Bytes, .one `Sim.RealSide, .one `Sim.Full, .one `Sim.X25519]

/-- Checks that fail the build on a wrong result: the axiom lists (`#guard_msgs`) and the
reference test vectors (`#guard`). -/
@[default_target] lean_lib Checks where
  globs := #[.one `Sim.Axioms, .one `Sim.AxiomsDischarge, .one `Sim.AxiomsFull,
    .one `Sim.RefVectors]
