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

/-- Lemmas about the real code that do not depend on a reference program: bytes and their
value (`DalekSim.Bytes`), limb bounds and `Result` lemmas (`DalekSim.Basic`), the slice
`ct_eq` on 32 bytes (`DalekSim.Choice`) and the Edwards group law (`DalekSim.Edwards`). -/
@[default_target] lean_lib DalekSim where
  globs := #[.submodules `DalekSim]
