import Lake
open Lake DSL

package «dynamic-dimensional-reduction» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "a40ffead0cc9abcfc25ab00544a772d4339edf8d"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The comparator audit surfaces (`DimRedAudit/*/Challenge.lean`,
`DimRedAudit/*/SolutionBasic.lean`, `DimRedAudit/*/Solution.lean` and
`DimRedAudit/Support/`).  Deliberately **not** a default target: it builds only on demand
(`lake build DimRedAudit`), so the ordinary project build is unchanged. -/
lean_lib «DimRedAudit» where
  globs := #[.submodules `DimRedAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «DimRed» where
  globs := #[.andSubmodules `DimRed]
