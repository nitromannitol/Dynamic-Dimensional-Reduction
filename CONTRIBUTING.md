# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively solicited
collaborative project, but issues and pull requests are welcome.

The shared analytic library comes from the separate
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) library, which
`lakefile.lean` requires as a `git` dependency pinned to an exact commit; Lake materializes it
under `.lake/packages/lattice-probability`.  It is read-only for this project: lattice objects
that do not depend on this paper belong in that library, and everything specific to the paper
belongs under `DimRed/`.  Contributors must not edit the dependency's sources.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib oleans
lake build           # build the dependencies and the library
lake build Audit     # the Mathlib-only comparator surface (not a default target)
```

The production build is required to emit no Lean or linter warnings.  The only `sorry`s are
the ten intentional statement-level ones in the `Challenge.lean` files under `Audit/`, each
checked against its completed `Solution.lean` by `leanprover/comparator`; see
[`Audit/README.md`](Audit/README.md).  Run `python3 tools/verify.py` from the repository root
for every gate (`--skip-lake` for the pure-Python ones), or
`cd tools/leanform && python3 -m leanform_tools.<gate> ../..` for one.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the `mathlib` and `Lattice-Probability` oleans and
  forces a multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/DimRed` (and the corresponding
  `.lake/build/ir/DimRed`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so `touch` does
  nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `DimRed/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`.  A change there is reported by the `check_manifest` gate and must
  be recorded in the manifest; the proofs after the end marker may be changed freely.

- **The main results** are in `DimRed/MainTheorems.lean`.  The axiom report is
  `lake build DimRed.Meta.AxiomsAudit`; `python3 tools/verify.py` runs every checker.

- **The comparator surface** under `Audit/` is deliberately not a default target.  Run
  `bash Audit/check_standalone.sh --vocabulary` after editing a challenge or
  `Audit/Support/Vocabulary.lean`; the vocabulary block must stay byte-identical in the four
  challenges and in the support file.  `lake env lean` does not read the options of
  `lakefile.lean`, so `Audit/check_standalone.sh` passes them explicitly; elaborate a single
  file standalone with `-DautoImplicit=false` in the same way.

## Elaboration policy for new files

These rules keep the build fast and predictable.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith`.
  This development works over `ℤ`, `ℕ` and `ℕ∞`; a new file that brings in `Real.rpow` or
  `Real.exp` should hoist each nonlinear fact into a small `private` lemma over abstract real
  variables, so that those terms never enter a numeric tactic.
- Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the
  bound names; otherwise the let-bodies are unfolded inside the tactic.
- Profile before restructuring: `lake env lean -DautoImplicit=false --profile <file>` on a
  warm tree, with `-Dprofiler.threshold=1` to expose diffuse costs.  Do not split a file or
  narrow its imports "for performance" without a profile before and after.
- Keep Lean files under 1500 lines.
- Never run `lake clean`.
