import Lake
open Lake DSL

require aeneas from "aeneas-backend"

package x25519sim where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target] lean_lib X25519Ref where
  globs := #[.submodules `X25519Ref]

@[default_target] lean_lib Curve25519Dalek where
  globs := #[.submodules `Curve25519Dalek]

@[default_target] lean_lib Sim where
  globs := #[.submodules `Sim]
