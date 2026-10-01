# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the main results of the
formalization of *Dynamic dimensional reduction in the Abelian sandpile* (Ahmed Bou-Rabee):
the three displays of Theorem 1.1 and the two clauses of Corollary 1.1.  Each comparator
lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `DimensionalReduction/` | Theorem 1.1(i), first display | `DimRed.StatementAudit.DimensionalReduction.dimensional_reduction` | `DimRed.dimensional_reduction` |
| | Theorem 1.1(i), second display | `DimRed.StatementAudit.DimensionalReduction.terminal_dimensional_reduction` | `DimRed.terminal_dimensional_reduction` |
| `SelfSimilarity/` | Theorem 1.1(ii) | `DimRed.StatementAudit.SelfSimilarity.self_similarity` | `DimRed.self_similarity` |
| `Sandpile/` | Corollary 1.1(i) | `DimRed.StatementAudit.Sandpile.sandpile_dimensional_reduction` | `DimRed.sandpile_dimensional_reduction` |
| | Corollary 1.1(ii) | `DimRed.StatementAudit.Sandpile.sandpile_self_similarity` | `DimRed.sandpile_self_similarity` |

The library theorems are those of [`DimRed/MainTheorems.lean`](../DimRed/MainTheorems.lean),
which restate the certified statements `DimRed.Frozen.*` unchanged.  Each directory's
`comparator.json` lists the theorems of its challenge.

## The Pattern

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition needed
to read its theorems, states them, and ends each with one intentional `sorry`, the proof
being checked.  The definitions form one vocabulary block, between `-- VOCABULARY-BEGIN` and
`-- VOCABULARY-END`, byte-identical in the three challenges, in the namespace
`DimRed.StatementAudit`: the sites and unit vectors of `ℤ^d`, the hypercube `C_N^{(d)}` and
its inner boundary, the sorted fundamental domain `S_M^{(d)}`, the neighbour sum and the
Laplacian with dissipating boundary conditions, the parallel toppling odometer and sandpile
of a general initial pile and of the paper's `s_0 ≡ 2d`, the terminal odometer and
sandpile, and the topple time `τ_j`.

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

`nbrSum` is the integer-valued neighbour sum of `DimRed/Support/Basic.lean`, not the
real-valued one of `LatticeProb/Site.lean`.  `Fin.snoc`, `Finset.Icc` on `Fin d → ℤ`,
`ENat.toNat`, `sInf` and `⨆` in `ℕ∞` are Mathlib's.

## How The Statements Read The Paper

The comparator checks that the library proves exactly the displayed statements over
definitions that can be read without the library; it does not check the vocabulary against
the paper.  The readings a reader has to accept are these, each recorded in the docstring of
the corresponding frozen statement and in [`CORRESPONDENCE.md`](../CORRESPONDENCE.md):

1. The hypercube of side `N` is the box `[1 - ⌊N/2⌋, ⌈N/2⌉]^d`, which is the paper's
   embedding for both parities (`dimred.tex:277`), and `M = ⌈N/2⌉` is `sideHalf N`.
2. The odometer is defined by the closed recursion
   `v_{t+1}(x) = v_t(x) + 1{s₀(x) + Δ v_t(x) ≥ 2d}` on the cube, `0` off it, which is the
   paper's two-line recursion (`dimred.tex:93-97`) with `s_t` replaced by `s₀ + Δ v_t`; the
   sandpile is `s_t = s₀ + Δ v_t`.
3. The terminal odometer `v_∞` is the supremum of `v_t` in `ℕ∞`, and the terminal sandpile
   is the integer `2d + Δ v_∞`, `v_∞` read through `ℕ∞ → ℕ`.  The topple time `τ_j` is an
   infimum in `ℕ∞`, `⊤` when no such time exists.
4. In the dimensional reduction statements the dimension is written `d + 1` in place of the
   paper's `d`, so the paper's `d ≥ 2` is `1 ≤ d`; `(x_{d-1}, c)` is `Fin.snoc x c`.
   Vector inequalities and the subtraction of a scalar from a vector are coordinatewise
   (`dimred.tex:273`).

Relative to the theorems of `DimRed/MainTheorems.lean` there are no presentation deltas:
each challenge theorem is the library statement with every repository name replaced by its
vocabulary copy.

## Solutions

The comparator checks that the solution theorem has the same elaborated type as the
challenge theorem, constant by constant through the whole dependency closure, so the
vocabulary must elaborate in the solution exactly as in the challenge.  It is therefore
compiled in `Support/Vocabulary.lean`, a verbatim copy of the block that imports only
Mathlib (the analogue of a per-challenge `SolutionBasic.lean`; one copy serves the three
solutions because the block is shared).  Each `Solution.lean` imports the repository, the
vocabulary and `Support/Bridge.lean`, restates the challenge theorems byte for byte, and
proves them by rewriting with the bridges and applying the library theorem.

The vocabulary declares no new type (`Site d` is `Fin d → ℤ` on both sides), so the bridges
in `Support/Bridge.lean` are short: `sideHalf`, `inSimplex`, `innerBoundary` and `lap` agree
with the repository's by `rfl`; `odo_eq` is an induction on time; `odoUnif_eq`,
`sandpUnif_eq`, `odoInfUnif_eq`, `sandpInfUnif_eq` and `toppleTime_eq` follow from it by
rewriting.

## Reproducing The Checks

The `Audit` library is not a default target: `lake build` and `lake build DimRed` do not
build it.  The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against this
repository's Mathlib:

```bash
bash Audit/check_standalone.sh Audit/DimensionalReduction/Challenge.lean
bash Audit/check_standalone.sh Audit/SelfSimilarity/Challenge.lean
bash Audit/check_standalone.sh Audit/Sandpile/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning per
challenge theorem; the last command checks that the vocabulary block is the same in the
three challenges and in `Support/Vocabulary.lean`.  The solutions build with
`lake build Audit`.  Then, with `leanprover/comparator`, `lean4export` (at the toolchain's
tag) and `landrun` built (see [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
for the pinned revisions), from the repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/<X>/comparator.json
```

expecting the acceptance line `Your solution is okay!`.  The workflow runs the same check on
every pair on request, with the independent nanoda kernel enabled as well.

**Status.**  The three solutions build, each solution theorem has the elaborated type of its
challenge theorem and mentions no repository constant, and each depends only on `propext`,
`Classical.choice` and `Quot.sound`.  `leanprover/comparator` itself was run on the three
pairs on 2026-09-30 at commit `c079868`, and re-run on 2026-10-01 at commit `e4f5a9b`, once
with the Lean kernel and once with the independent nanoda kernel enabled as well (a
temporary copy of `comparator.json` with `"enable_nanoda": true`); all six runs printed
`Your solution is okay!` in both sweeps.
