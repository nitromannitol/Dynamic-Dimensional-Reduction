# The comparator challenges

This directory contains Mathlib-only comparator challenges for the main results of the
formalization of *Dynamic dimensional reduction in the Abelian sandpile* (Ahmed Bou-Rabee):
the three displays of Theorem 1.1, the two clauses of Corollary 1.1 and the five clauses of
Proposition 4.1.  Each comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `DimensionalReduction/` | Theorem 1.1(i), first display | `DimRed.StatementAudit.DimensionalReduction.dimensional_reduction` | `DimRed.dimensional_reduction` |
| | Theorem 1.1(i), second display | `DimRed.StatementAudit.DimensionalReduction.terminal_dimensional_reduction` | `DimRed.terminal_dimensional_reduction` |
| `SelfSimilarity/` | Theorem 1.1(ii) | `DimRed.StatementAudit.SelfSimilarity.self_similarity` | `DimRed.self_similarity` |
| `Sandpile/` | Corollary 1.1(i) | `DimRed.StatementAudit.Sandpile.sandpile_dimensional_reduction` | `DimRed.sandpile_dimensional_reduction` |
| | Corollary 1.1(ii) | `DimRed.StatementAudit.Sandpile.sandpile_self_similarity` | `DimRed.sandpile_self_similarity` |
| `Regularity/` | Proposition 4.1, self-similarity | `DimRed.StatementAudit.Regularity.base_dimension_consistency` | `DimRed.base_dimension_consistency` |
| | Proposition 4.1, weak facet | `DimRed.StatementAudit.Regularity.base_dimension_weak_compatibility` | `DimRed.base_dimension_weak_compatibility` |
| | Proposition 4.1, strong derivative | `DimRed.StatementAudit.Regularity.base_dimension_strong_derivative` | `DimRed.base_dimension_strong_derivative` |
| | Proposition 4.1, strong facet | `DimRed.StatementAudit.Regularity.base_dimension_strong_compatibility` | `DimRed.base_dimension_strong_compatibility` |
| | Proposition 4.1, strong topple | `DimRed.StatementAudit.Regularity.base_dimension_strong_topple` | `DimRed.base_dimension_strong_topple` |

The library theorems are those of [`DimRed/MainTheorems.lean`](../DimRed/MainTheorems.lean),
which restate the statements `DimRed.Frozen.*` unchanged.  Each directory's
`comparator.json` lists the theorems of its challenge.

## The Pattern

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition needed
to read its theorems, states them, and ends each with one intentional `sorry`, the proof
being checked.  The definitions form one vocabulary block, between `-- VOCABULARY-BEGIN` and
`-- VOCABULARY-END`, byte-identical in the four challenges and in the four `SolutionBasic.lean`
files, in the namespace `DimRed.StatementAudit`: the sites and unit vectors of `ℤ^d`, the
hypercube `C_N^{(d)}` and its inner boundary, the sorted fundamental domain `S_M^{(d)}`, the
neighbour sum and the Laplacian with dissipating boundary conditions, the parallel toppling
odometer and sandpile of a general initial pile and of the paper's `s_0 ≡ 2d`, the terminal
odometer and sandpile, the topple time `τ_j`, the facet point and the simplex maximum.

No theorem has a hypothesis beyond those of the paper's statement: nothing from the
literature is assumed, so the challenges carry no assumed result.

## Definition Provenance

The challenge definitions are statement-level copies of the repository definitions, token
for token.

| Challenge declaration | Repository source |
| --- | --- |
| `Site`, `unit` | `LatticeProb/Site.lean` (the `lattice-probability` dependency) |
| `loCoord`, `sideHalf`, `hiCoord`, `inCube` (and its `DecidablePred` instance), `inSimplex`, `cube`, `innerBoundary` | `DimRed/Support/Basic.lean` |
| `nbrSum`, `lap`, `odo`, `sandp`, `odoUnif`, `sandpUnif`, `odoInf`, `odoInfUnif`, `sandpInfUnif`, `toppleTime` | `DimRed/Support/Basic.lean` |
| `simplex`, `simplexMax`, `facetPoint` | `DimRed/Support/Basic.lean` |

`nbrSum` is the integer-valued neighbour sum of `DimRed/Support/Basic.lean`, not the
real-valued one of `LatticeProb/Site.lean`.  `Fin.snoc`, `Finset.Icc` on `Fin d → ℤ`,
`ENat.toNat`, `sInf` and `⨆` in `ℕ∞` are Mathlib's.

## How The Statements Read The Paper

The comparator checks that the library proves exactly the displayed statements over
definitions that can be read without the library; it does not check the vocabulary against
the paper.  The readings a reader has to accept are these, each recorded in the docstring of
the corresponding frozen statement and in [`CORRESPONDENCE.md`](../CORRESPONDENCE.md):

1. The hypercube of side `N` is the box `[1 - ⌊N/2⌋, ⌈N/2⌉]^d`, which is the paper's
   embedding for both parities (`dimred-corrected-arxiv.tex:279`), and `M = ⌈N/2⌉` is `sideHalf N`.
2. The odometer is defined by the closed recursion
   `v_{t+1}(x) = v_t(x) + 1{s₀(x) + Δ v_t(x) ≥ 2d}` on the cube, `0` off it, which is the
   paper's two-line recursion (`dimred-corrected-arxiv.tex:93-97`) with `s_t` replaced by `s₀ + Δ v_t`; the
   sandpile is `s_t = s₀ + Δ v_t`.
3. The terminal odometer `v_∞` is the supremum of `v_t` in `ℕ∞`, and the terminal sandpile
   is the integer `2d + Δ v_∞`, `v_∞` read through `ℕ∞ → ℕ`.  The topple time `τ_j` is an
   infimum in `ℕ∞`, `⊤` when no such time exists.
4. In the dimensional reduction statements the dimension is written `d + 1` in place of the
   paper's `d`, so the paper's `d ≥ 2` is `1 ≤ d`; `(x_{d-1}, c)` is `Fin.snoc x c`.
   Vector inequalities and the subtraction of a scalar from a vector are coordinatewise
   (`dimred-corrected-arxiv.tex:275`).

Relative to the theorems of `DimRed/MainTheorems.lean`, each challenge theorem is the library
statement with every repository name replaced by its vocabulary copy, with one difference of
presentation: Corollary 1.1 and the strong topple control clause of Proposition 4.1 are stated
over `sandpInfUnif`, `sandpUnif` and `simplexMax`, where the library statements use
`DimRed.Corrected.terminalPile`, `DimRed.Corrected.pile` and `DimRed.Corrected.maximum` on
subtype carriers. The two agree by `rfl` and by `DimRed.Corrected.maximum_eq_simplexMax`.

## Solutions

The comparator checks that the solution theorem has the same elaborated type as the
challenge theorem, constant by constant through the whole dependency closure, so the
vocabulary must elaborate in the solution exactly as in the challenge.  Each pair therefore
has a `SolutionBasic.lean`, a verbatim copy of the vocabulary block of its `Challenge.lean`
that imports only Mathlib.  Each `Solution.lean` imports the repository, the `SolutionBasic`
of its pair and the bridge of its pair in `Support/`, restates the challenge theorems byte
for byte, and proves them by rewriting with the bridges and applying the library theorem.

The four bridges are `Support/DimensionalReductionBridge.lean`,
`Support/SelfSimilarityBridge.lean`, `Support/SandpileBridge.lean` and
`Support/RegularityBridge.lean`.  The vocabulary declares no new type (`Site d` is
`Fin d → ℤ` on both sides), so the bridges are short: `innerBoundary_eq` and `lap_eq` agree
with the repository's by `rfl`; `odo_eq` is an induction on time; `odoUnif_eq`,
`sandpUnif_eq`, `odoInfUnif_eq`, `sandpInfUnif_eq` and `toppleTime_eq` follow from it by
rewriting; `simplex` and `simplexMax` are non-recursive and agree by unfolding, which
`simplex_eq` and `simplexMax_eq` record.  A bridge keeps only the lemmas its solution uses,
with those they depend on.  [`DESIGN.md`](DESIGN.md) describes the four files of a pair.

## Reproducing The Checks

The `DimRedAudit` library is not a default target: `lake build` and `lake build DimRed` do
not build it.  The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against this
repository's Mathlib:

```bash
bash DimRedAudit/check_standalone.sh DimRedAudit/DimensionalReduction/Challenge.lean
bash DimRedAudit/check_standalone.sh DimRedAudit/SelfSimilarity/Challenge.lean
bash DimRedAudit/check_standalone.sh DimRedAudit/Sandpile/Challenge.lean
bash DimRedAudit/check_standalone.sh DimRedAudit/Regularity/Challenge.lean
bash DimRedAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic, per pair
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning per
challenge theorem; the last command checks that the vocabulary block is byte-identical in
each `Challenge.lean` and in the `SolutionBasic.lean` beside it.  The solutions build with
`lake build DimRedAudit`.  Then, with `leanprover/comparator`, `lean4export` (at the
toolchain's tag), `nanoda` and `landrun` built at the pins below (see also
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)), from the
repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator DimRedAudit/<X>/comparator.json
```

expecting the acceptance line `Your solution is okay!`.  The workflow runs the same check on
every pair on request.

## Comparator Runs

The official `leanprover/comparator` was run on every pair in this directory on a local
machine, with the Lean kernel and the independent `nanoda` kernel both enabled (every committed
`comparator.json` sets `"enable_nanoda": true`), at these pins:

| tool | revision |
| --- | --- |
| `leanprover/comparator` | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| `lean4export` | `v4.32.0`, the tag of `lean-toolchain` |
| `nanoda` (`ammkrn/nanoda_lib`) | `6ae1f0cd962f081f6c423454c5da729d841236a7` |
| `landrun` | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

A pass means the comparator printed

```
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

so the solution proves a theorem whose statement and full dependency closure match the
challenge's, using only the permitted axioms, and is accepted by both the independent nanoda
kernel and Lean's default kernel.

### `DimensionalReduction`

| Check | Result |
| --- | --- |
| Lean and nanoda kernels | passed (60 s) |

### `SelfSimilarity`

| Check | Result |
| --- | --- |
| Lean and nanoda kernels | passed (164 s) |

### `Sandpile`

| Check | Result |
| --- | --- |
| Lean and nanoda kernels | passed (106 s) |

### `Regularity`

| Check | Result |
| --- | --- |
| Lean and nanoda kernels | passed (59 s) |

**Status.**  All 23 theorem-level statements of the corrected edition (its versions of the 20 statement clauses of the published paper, and three added lemmas) are proved in Lean, with no `sorry` and only the standard axioms. Theorem 1.1 and Corollary 1.1 are stated as published, with the quantifier in the definition of `τ_j` made explicit. The four pairs here
check Theorem 1.1, Corollary 1.1 and Proposition 4.1; the other results (Sections 2 and 3 and
Lemmas 4.1 and 5.1) have no comparator pair.
