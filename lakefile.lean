import Lake
open Lake DSL

def moreServerArgs := #[
  "-DautoImplicit=false",
  "-Dhygiene=false",
  "-Dhygiene=false",
  "-Dlinter.unusedVariables=false",
  "-Dpp.structureProjections=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package «CGBF» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"ac0730e"

@[default_target]
lean_lib «CGBF» where
  srcDir := "src"
  moreLeanArgs := moreLeanArgs
