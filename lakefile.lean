import Lake
open Lake DSL

package «substrate-undecidability-lean» where
  -- NEMS suite: internal undecidability of substrate discreteness (Part I Lean)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib Substrate where
