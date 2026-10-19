import DimRed.Support.AxisStep
import DimRed.Support.Fundamental

open LatticeProb DimRed

namespace DimRed

/-- At a coordinate equal to two, the `-unit` neighbour of the shifted point has
the same odometer at the smaller scale as the shifted point itself: the two are
reflections of each other in the hyperplane `x_k = 1` of the smaller cube, and
the odometer is invariant under that reflection (`odo_reflect_coord`).  This is
the paper's reflectional-symmetry step, `dimred-corrected-arxiv.tex`. -/
theorem odoUnif_sub_unit_shift_eq (d m t : ℕ) (y : Site d) (k : Fin d)
    (hk : y k = 2) :
    odoUnif d (2 * (m - 1)) t (fun j => (y - unit k) j - 1)
      = odoUnif d (2 * (m - 1)) t (fun j => y j - 1) := by
  -- the reflection `x_k ↦ 1 - x_k` of the smaller cube sends `y - 1` to
  -- `(y - unit k) - 1`, because `y k - 1 = 1` reflects to `0 = y k - 2`
  have hrefl : (fun j => if j = k then 1 - (y k - 1) else y j - 1)
      = fun j => (y - unit k) j - 1 := by
    funext j
    by_cases hj : j = k
    · subst hj
      rw [if_pos rfl, sub_unit_self]
      have h : y j = 2 := hk
      rw [h]
      norm_num
    · rw [if_neg hj, sub_unit_other _ _ _ _ hj]
  rw [← hrefl]
  simp only [odoUnif]
  exact odo_reflect_coord d (m - 1) (2 * (d : ℤ)) t (fun j => y j - 1) k

end DimRed
