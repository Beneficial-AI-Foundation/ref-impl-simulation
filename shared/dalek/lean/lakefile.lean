import Lake
open Lake DSL

require aeneas from "aeneas-backend"
require PrimeCert from "primecert"

package dalek where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- curve25519-dalek: the Aeneas output of `../extract.sh` (Funs, Types), the hand-written
external definitions (FunsExternal, TypesExternal), support files from
curve25519-dalek-lean-verify (Math, Auxiliary), and the field specs (Specs). -/
@[default_target] lean_lib Curve25519Dalek where
  globs := #[.submodules `Curve25519Dalek]
