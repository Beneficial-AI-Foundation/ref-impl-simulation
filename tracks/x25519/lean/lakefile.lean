import Lake
open Lake DSL

/-- The shared curve25519-dalek library (`shared/dalek`). It brings Aeneas and PrimeCert. -/
require dalek from "../../../shared/dalek/lean"

package x25519sim where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- One copy of Mathlib and the other packages for the library and both tracks.
  packagesDir := "../../../shared/dalek/lean/.lake/packages"

/-- Reference: Aeneas output of `ref-plain` plus the hand-written ZMod p field model. -/
@[default_target] lean_lib X25519Ref where
  globs := #[.submodules `X25519Ref]

/-- Real: Aeneas output of x25519-dalek's `x25519`. Its two external functions are the
definitions in `Curve25519Dalek.Funs` of the shared library. -/
@[default_target] lean_lib X25519Dalek where
  globs := #[.submodules `X25519Dalek]

@[default_target] lean_lib Sim where
  globs := #[.one `Sim.Pilot, .one `Sim.Discharge, .one `Sim.LadderMath, .one `Sim.RefSide,
    .one `Sim.Bytes, .one `Sim.RealSide, .one `Sim.Full, .one `Sim.X25519]

/-- Checks that fail the build on a wrong result: the axiom lists (`#guard_msgs`) and the
reference test vectors (`#guard`). -/
@[default_target] lean_lib Checks where
  globs := #[.one `Sim.Axioms, .one `Sim.AxiomsDischarge, .one `Sim.AxiomsFull,
    .one `Sim.RefVectors]
