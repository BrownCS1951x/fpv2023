import Lake

open Lake DSL

def extraArgs := #["-DautoImplicit=false", "-Dlinter.unusedVariables=false"]

package love {
  moreServerArgs := extraArgs
}

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
  moreLeanArgs := extraArgs 
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "ba80034619884735df10ebb449b4fc2a44b2c3e7"
require autograder from git "https://github.com/robertylewis/lean4-autograder-main" @ "d1fcb4ce126aa074f5e35514c0754d43486b7b22"
  