import Lake
open Lake DSL

package «verified-compiler» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.unusedVariables, false⟩]

@[default_target]
lean_lib VerifiedCompiler where
  globs := #[Glob.submodules `VerifiedCompiler]
