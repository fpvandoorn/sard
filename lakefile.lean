import Lake
open Lake DSL

package «sard» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "MR-sigma-compact-measure-zero"

@[default_target]
lean_lib «Sard» {
  -- add any library configuration options here
}
