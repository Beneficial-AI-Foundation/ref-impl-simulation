import Lake
open Lake DSL

require aeneas from "aeneas-backend"

package «chachaSim» where

lean_lib Ref where
  globs := #[.submodules `Ref]

lean_lib Real where
  globs := #[.submodules `Real]

lean_lib RealAead where
  globs := #[.submodules `RealAead]

@[default_target] lean_lib Sim where
  globs := #[.andSubmodules `Sim]
