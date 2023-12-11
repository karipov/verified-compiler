import Lake
open Lake DSL

def extraArgs := #["-DautoImplicit=false", "-Dlinter.unusedVariables=false"]

package «verified-compiler» {
  moreServerArgs := extraArgs
}

@[default_target]
lean_lib VerifiedCompiler {
  roots := #[`VerifiedCompiler]
  globs := #[Glob.submodules `VerifiedCompiler]
  moreLeanArgs := extraArgs
}


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "ba80034619884735df10ebb449b4fc2a44b2c3e7"
