# Contributing and building

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
lake exe cache get      # first time: prebuilt Mathlib oleans
lake build              # build the dependencies and the library
lake build DimRedAudit  # the Mathlib-only comparator surface (not a default target)
```

The production build is required to emit no Lean or linter warnings.  The only `sorry`s are
the ten intentional statement-level ones in the `Challenge.lean` files under `DimRedAudit/`,
each checked against its completed `Solution.lean` by `leanprover/comparator`; see
[`DimRedAudit/README.md`](DimRedAudit/README.md).  Run `python3 tools/verify.py` from the
repository root for every check (`--skip-lake` for the pure-Python ones), or
`cd tools/leanform && python3 -m leanform_tools.<check> ../..` for one.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the `mathlib` and `Lattice-Probability` oleans and
  forces a multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/DimRed` (and the corresponding
  `.lake/build/ir/DimRed`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so `touch` does
  nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `DimRed/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`.  A change there is reported by the `check_manifest` check and must
  be recorded in the manifest; the proofs after the end marker may be changed freely.

- **The main results** are in `DimRed/MainTheorems.lean`.  The axiom report is
  `lake build DimRed.Meta.AxiomsAudit`; `python3 tools/verify.py` runs every checker.

- **The comparator surface** under `DimRedAudit/` is deliberately not a default target.  Run
  `bash DimRedAudit/check_standalone.sh --vocabulary` after editing a challenge or its
  `SolutionBasic.lean`; the vocabulary block must stay byte-identical in each challenge and in
  the `SolutionBasic.lean` of the same pair.  `lake env lean` does not read the options of
  `lakefile.lean`, so `DimRedAudit/check_standalone.sh` passes them explicitly; elaborate a
  single file standalone with `-DautoImplicit=false` in the same way.

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

## Checks

The checks are in `tools/leanform/`, a vendored copy of a shared checker package; they need
Python 3.10 or newer and PyYAML (`python3 -m pip install -r tools/requirements.txt`).
`python3 tools/verify.py` runs all of them and fails on the first failure.

| check (`python3 -m leanform_tools.<check> <repo-path>`, from `tools/leanform/`) | what it verifies |
|---|---|
| `check_manifest` | every statement file in `DimRed/Frozen/` holds exactly one block whose SHA-256 equals the one in `ledger/manifest.yaml` and which declares exactly the recorded declaration; `DimRed/` contains no `axiom`, `admit` or `sorryAx` and no `sorry` |
| `check_axioms` | prints the axiom closure of every recorded declaration and fails if one contains `sorryAx` |
| `check_warnings` | `lake build DimRed` emits no warning |
| `check_constants` | in a statement whose conclusion has an existential constant, the constant is bound before the paper's parameters |
| `check_coverage` | every theorem, lemma, proposition and corollary of the corrected edition is named in the `source` of some statement |
| `check_clauses` | compares the number of assertions of each paper statement with the conjuncts of its Lean statement, against the reading in `ledger/readings.yaml` |
| `check_exponents` | compares the exponents of a paper statement with those of its Lean statement, against `ledger/readings.yaml` |
| `paper_anchors`, `paper_citations` | the `<file>.tex:<lines>` references in the manifest and in the headers of `DimRed/Frozen/` point at the cited labels; other comments cite the edition by label only |
| `sync_docs` | the generated status block of `README.md` and the statement table of `CORRESPONDENCE.md` agree with the manifest (`--write` regenerates them) |
| `assumptions`, `certificate` | `ASSUMPTIONS.md` and `CERTIFICATE.md` are current (`--check`) |

`scripts/check_axioms.py` checks the output of `lake build DimRed.Meta.AxiomsAudit` against an
explicit list of theorems: each must depend on exactly `propext`, `Classical.choice` and
`Quot.sound`, and a missing, unexpected or repeated report fails.

## Comparators

Each pair under `DimRedAudit/` has a Mathlib-only `Challenge.lean`, a `SolutionBasic.lean` with
its vocabulary, a `Solution.lean` that proves the same statements from the library, and a
`comparator.json` that permits exactly `propext`, `Classical.choice` and `Quot.sound`. Do not
change a challenge without checking it against the paper's statement. Run the comparator as
described in the README; a missing pair, a missing tool or a failed kernel check is a failure.

## Continuous integration

`.github/workflows/build.yml` runs on pushes to `main` that change code or build configuration,
and on manual dispatch: it builds the library with zero warnings, checks the axiom report
against the explicit list and runs `tools/verify.py`. `.github/workflows/comparator.yml` runs
the four comparator pairs on manual dispatch.
