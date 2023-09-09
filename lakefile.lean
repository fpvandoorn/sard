import Lake
open Lake DSL

package «sard» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fix_minimize_imports"

@[default_target]
lean_lib «Sard» {
  -- add any library configuration options here
}
