# Decisions

Rulings that change what the development proves, with the evidence for each.

## D1. The strong-facet comparison of `dimred.tex:1288-1296` is replaced

**Ruling (owner, 2026-09-27):** the comparison
`eq:laplace_11 >= eq:laplace_21` is a defect in the paper's argument and is to be
fixed in `paper/dimred.tex`; frozen statements stay unchanged.

**Evidence.**  The paper's chain gives
`v_t(x_i - e_{j'}, 2, 1_j) >= v_{t-1}(x_i, 1, 1_j)`, but `eq:laplace_21`'s term
is `v_{t-1}(x_i - e_{j'}, 1, 1_j)`.  Closing the gap needs
`v_{t-1}(x_i, 1, 1_j) >= v_{t-1}(x_i - e_{j'}, 1, 1_j)`, which is the opposite of
axis monotonicity and is false: measured on the paper's own dynamics for
`j <= 2`, `M <= 6` and every `t`, 145 failures, e.g. `j = 0`, `M = 2`, `t = 3`:
`v_{t-1}(2,1) = 1 < 2 = v_{t-1}(1,1)`.  The sum inequality itself fails: 40
failures, e.g. `j = 0`, `M = 4`, `t = 17`: left `16`, right `17`.

**Repair.**  The development does not use the comparison.  The gap one step back
in time, which is what the unit-gap branch of dimensional reduction needs, follows
from the gap at the current time and the first-difference bound of Corollary 2.2:
`DimRed.odo_jump_of_gap` (`DimRed/Support/RegBridges.lean`).  The strong-facet
clause itself is the first-difference bound at a coordinate equal to one, which is
Corollary 2.2 directly: `DimRed.strong_facet_step_of_reg`
(`DimRed/Support/RegBridges.lean`).  Neither uses the paper's comparison.

**Consequence.**  `DimRed.FacetTermBounds` and `DimRed.lap_facet_le_of_prev`
(`DimRed/Support/RegFacetStep.lean`) formalize the defective comparison and are
off the critical path; they are retained only as a record of the paper's text and
are not used by the induction.

## Record (2026-09-30): how the strong-facet clause was proved

This is a record for the owner, not a ruling.  The ruling of 2026-09-27 above stands
as written: the paper's argument is repaired and no frozen statement changes.  Two of
its details turned out differently when the step was proved:

* `DimRed.strong_facet_step_of_reg` and `DimRed.odo_jump_of_gap` give only the bound
  `v_t(x,1,1_j) - v_t(x,2,1_j) <= 1`; they do not give the clause.  The clause is
  proved by `DimRed.facet_step_of_earlier` (`DimRed/Support/FacetStepFinal.lean`).
  Under the gap `v_t(p1) = v_t(p2) + 1`, the clause at `t - 1` together with the
  first-difference bound forces the gap at `t - 1` to be `0`, with `p1` toppling at
  `t - 1`.  A neighbour-by-neighbour Laplacian comparison, `Δv_t(p2) >= Δv_{t-1}(p1)`,
  then shows that `p2` topples at `t`.  Strong topple control at `t - 1` keeps `p1`
  fixed when `t - 1 >= τ_{M-1}`; before that time the gap cannot occur.
* The measured failures of `eq:laplace_11 >= eq:laplace_21` quoted above all lie
  outside the clause's gap hypothesis.  Under the gap, the comparison holds termwise:
  0 failures in 311 gap instances (`d <= 4`, `M <= 6`; `scratch/facet/t2.py`), and 0 in
  723 (`d <= 4`, `M <= 7`) and 671 (`d <= 5`, `M <= 6`) gap instances in the extended
  check (`ledger/audits/2026-10-01-extended-refutation.md`).  So the
  paper's comparison is wrong only as stated without the gap.  The corrected paper's
  sentence that the clause "is Corollary 2.2 directly" (CHANGES_FROM_ARXIV.md, last
  section) should be revisited by the owner.  On 2026-10-01 that last section was
  corrected to attribute the clause to `facet_step_of_earlier` and the gap step to
  `odo_jump_of_gap`, so the erratum no longer names `strong_facet_step_of_reg` for
  the clause; the owner's confirmation of the paper's narrative remains open.
* `DimRed.FacetTermBounds` and `DimRed.lap_facet_le_of_prev` remain unused.  Their
  `gap` field (a gap at `t - 1`) is false whenever the clause's hypotheses hold.

## Record (2026-09-30): reading of the strong derivative clause

This is a record for the owner, not a ruling.  At `dimred.tex:929-931` the paper leaves
the bold `x` of the strong derivative clause unbound.  The frozen statement
`prop-base-dimension-strong-derivative` reads it as the facet point `(x_i, 1, 1_j)`.
That is how the paper uses the bound (`dimred.tex:1263-1265`, the step "taking x = 1"
at `dimred.tex:1029`, and CHANGES_FROM_ARXIV.md §9).  The broader reading over all of
`S_M` is false: `d = 1`, `M = 4`, `t = 9 < τ_4 = 13` gives
`v_9(2) - v_9(4) = 6 - 3 = 3 > 2`.  The refute-first seal audit
(`ledger/audits/2026-09-30-seal-audit.md`) failed to refute the facet-point reading.
The owner should confirm it.
