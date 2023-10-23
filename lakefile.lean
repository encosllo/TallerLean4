import Lake
open Lake DSL

package «TallerLean4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Paperproof from git
  "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

@[default_target]
lean_lib «TallerLean4» {
  -- add any library configuration options here
}
