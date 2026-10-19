# Corrected arXiv-format source

This separate edition of *Dynamic dimensional reduction in the Abelian sandpile*
starts from [arXiv v2](https://arxiv.org/abs/2009.05968v2). The official
[extraction](../dimred-arxiv.tex) and the historical local
[manuscript](../dimred.tex) are preserved byte-for-byte. The abstract is unchanged.

The assembled C01–C25 draft had SHA-256
`498f5bf593fc40bdc938032c7bfb69685d94d3f5abcb4720d310fd0be026d89a`.
This edition additionally reconciles C18's proof description with the joint
induction and removes its duplicated subsection heading. The independent
first-wait argument in C20 remains an alternative mathematical proof; the Lean
provider derives the closed C/S conclusions above the existing joint induction.
The manifest records this edition's exact source hash.

The changes below refer to the original arXiv extraction's line numbers.
They preserve each true printed conclusion and correct the specified false or
malformed assertions explicitly.

| Change | Original lines | Correction and reason |
|---|---|---|
| C01 | 128 | Define the boundary hitting time using **some** inner-boundary site, with an empty hitting set giving infinity; resolve the formerly unspecified quantifier. |
| C02 | 292 | Insert `max(0, floor(...))` in the point formula. Signed negative initial values invalidate the untruncated formula. Keep the upper-bound-only hypothesis. |
| C03 | 317–333 | Prove signed parabolic least action with zero truncation. Retain every nonnegative competitor, including arbitrary initial competitor values. |
| C04 | 369–404 | Define the folded threshold process independently, summing all directed neighbor occurrences and using the physical odd/even reflection. Replace the erroneous block-index algorithm and unrestricted floor update. |
| C05 | 419–429 | Prove both symmetry and folded-process identification by threshold induction, with cube-local initial symmetry and no height bound. |
| C06 | 481 | Require the translated site to be in the physical cube in the **first** boundary alternative. Preserve the all-index disjunction and its second alternative. |
| C07 | 494–508 | Use the integer strict/equality threshold argument for difference comparison at every constant integer height. |
| C08 | 514–526 | Replace false arbitrary unbalanced mixed moves by the true elementary reflection and rotation moves. Retain unrestricted constant heights. |
| C09 | 529–530 | Supply the direct threshold proof for elementary axis moves; equality compares every directed neighbor occurrence. The unrestricted Lean producer is `DimRed.Corrected.axis_monotonicity`. |
| C10 | 540–663 | Retain the true terminal-corner premise and all constant integer heights in the derivative bound; use direct firing comparisons at the reflecting and dissipating boundaries. |
| C11 | 679–692 | Replace the unrestricted floor argument for weak topple control by contraction of the physical threshold update; use cube-local symmetry and a nonempty maximum. Its unrestricted Lean successor is provided by `DimRed.Corrected.topple_limit`. |
| C12 | 779 | Define `a₀=a₁=d` so the first ripple window has a defined left endpoint. This creates no new firing assertion at time zero. |
| C13 | 798–800 | State the shifted ripple profile only while its shifted index is nonnegative, with a positive reference time. The old unlimited assertion is false. |
| C14 | 815–896 | Retain the separate block-edge term, correct the direction of the affine monotonicity, and include moving-front positions and adjacent windows in the ripple induction. Independent arithmetic checks support this text. |
| C15 | 924 | Repair the repeated-time tautology to the substantive no-fire conclusion used by the induction. |
| C16 | 927–930 | Bind the exact facet point and its dimension; the unbound broad reading of the constant-two bound is false. |
| C17 | 935 | Complete the missing tail subscript, preserving both compatibility conclusions. |
| C18 | 1262–1318 | Replace the false head-neighbor inference by the restricted C/S route. Reconcile the proof description with the dimension–side–time joint induction; use the early derivative and generic facet comparison for the empty head. Remove a duplicate heading introduced during assembly. |
| C19 | 1319–1333 | Correct the direction-index range and account for every directed boundary occurrence in the early two-step estimate. Retain its early-time restriction. |
| C20 | 1334–1362 | Withdraw the false full-domain Case 2 estimate and dissipating cap. State strict-head C and nonempty-head S, including both firing conclusions; keep only no-fire at the all-ones exception. |
| C21 | 1105–1110 | Label and register the true one-dimensional terminal profile and derivative, including the dissipating endpoint `x=M`. |
| C22 | 143 | Add the corollary coverage label without changing its assertion. |
| C23 | 706 | Add the no-reduction proposition's coverage label without changing its assertion. |
| C24 | 728 | Add the radial Laplacian's coverage label without changing its assertion. |
| C25 | 735–768 | Replace the removed block-index algorithm's use by the exact directed radial neighbor count, retaining zero endpoint coefficients. |

Piles in the source-facing API have physical cube carriers. Terminal piles
require positive dimension, and their integer odometer conversions are justified
by stabilization. Maxima require a nonempty domain. The folded process has
its own recursion and a proved identification with the physical odometer.
These definition repairs add no theorem coverage by themselves.

All inherited and added statement clauses have Lean statements in the
manifest. They were reviewed independently against this source, and the
integrated development passes the repository's verifier; see
[the integration record](../../ledger/audits/2026-10-19-corrected-source-integration.md).
This is not a certificate against the unchanged arXiv v2 text.

The bibliography and required figures are included. Build from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error dimred-corrected-arxiv.tex
```
