import Lake
open Lake DSL

package «chapter1» where
  -- add any package configuration options here

lean_lib «chapter1» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LinearAlgebraDoneRight» {
  -- add any library configuration options here
}
