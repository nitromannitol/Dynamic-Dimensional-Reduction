import Lake
open Lake DSL

package «dynamic-dimensional-reduction» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from ".." / "Lattice-Probability"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «DimRed» where
  globs := #[.andSubmodules `DimRed]
