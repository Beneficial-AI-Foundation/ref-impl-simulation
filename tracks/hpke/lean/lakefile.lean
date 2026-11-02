import Lake
open Lake DSL

require aeneas from "aeneas-backend"

package hpkesim where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target] lean_lib Shared
@[default_target] lean_lib Ref
@[default_target] lean_lib Real
@[default_target] lean_lib Sim

