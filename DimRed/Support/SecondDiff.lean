/-
The Laplacian as a sum of second differences, `dimred.tex:1210-1215`.  This is the
decomposition the self-similarity argument of Section 5 runs on: the identity between two
scales holds term by term in the directions the shift does not touch, and the remaining
directions are handled by the reflection at the origin.
-/
import DimRed.Support.DimRedStep
import DimRed.Frozen.Prelim.PtInd

namespace DimRed

open LatticeProb

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

/-- `dimred.tex:1215-1218`: the Laplacian is the sum of its coordinatewise
second differences. -/
theorem lap_eq_sum_second_diff {d : ℕ} (u : Site d → ℤ) (x : Site d) :
    lap u x = ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i)) := by
  simp only [lap, nbrSum]
  calc
    -(2 * (d : ℤ)) * u x + ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) =
      (∑ _i : Fin d, (-2 : ℤ) * u x) +
          ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ = ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring


end DimRed
