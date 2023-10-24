import Lake
open Lake DSL

package «linear_algebra_done_right» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LinearAlgebraDoneRight» {
  -- add any library configuration options here
}
