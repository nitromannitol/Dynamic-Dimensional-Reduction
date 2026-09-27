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
