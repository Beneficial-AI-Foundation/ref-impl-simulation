import Lake
open Lake DSL

/-- The shared curve25519-dalek library (`shared/dalek`). It brings Aeneas and PrimeCert. -/
require dalek from "../../../shared/dalek/lean"

package ristrettosim where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- One copy of Mathlib and the other packages for the library and both tracks.
  packagesDir := "../../../shared/dalek/lean/.lake/packages"

/-- Reference: Aeneas output of `ref-plain` plus the hand-written ZMod p field model. -/
@[default_target] lean_lib RistrettoRef where
  globs := #[.submodules `RistrettoRef]

@[default_target] lean_lib Sim where
  globs := #[.submodules `Sim]
