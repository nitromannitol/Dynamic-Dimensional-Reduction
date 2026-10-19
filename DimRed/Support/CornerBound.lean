/-
The corner bound below the topple time, with the time restriction removed.

`ToppleTime.odo_corner_lt_of_lt_toppleTime` needs `1 ≤ t`, because at `t = 0` the argument by
contradiction has nothing to contradict.  At `t = 0` the odometer is zero and the bound is
immediate, so the two cases together give the form the strong derivative clause consumes.
-/
import DimRed.Support.ToppleTime
import DimRed.Support.OneDimBoundaryAlt

namespace DimRed

open LatticeProb

/-- In dimension one the corner is the constant point `M`. -/
theorem cornerPoint_one (M : ℕ) : cornerPoint 1 M = fun _ => (M : ℤ) := by
  funext i
  fin_cases i
  simp [cornerPoint]

/-- The corner bound of `dimred-corrected-arxiv.tex`, at every time below the topple time. -/
theorem odo_corner_le_of_lt_toppleTime (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s : ℕ)
    (hs : (s : ℕ∞) < toppleTime d M) :
    odoUnif d (2 * M) s (cornerPoint d M) ≤ (M : ℤ) - 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · have h0 : odoUnif d (2 * M) 0 (cornerPoint d M) = 0 := rfl
    have : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  · exact odo_corner_lt_of_lt_toppleTime d M hd hM s hs hpos

/-- The one-dimensional strong derivative clause, with no hypothesis left. -/
theorem odo_one_strong_deriv_final (M t : ℕ) (hM : 2 ≤ M)
    (ht : (t : ℕ∞) < toppleTime 1 M)
    (y : Site 1) (hy1 : 1 ≤ y 0) (hyM : y 0 ≤ (M : ℤ)) :
    odoUnif 1 (2 * M) t y - odoUnif 1 (2 * M) t (y + unit 0 + unit 0) ≤ 2 * y 0 := by
  refine odo_one_strong_deriv_uncond M t hM ht ?_ y hy1 hyM
  intro s hs
  have h := odo_corner_le_of_lt_toppleTime 1 M (by omega) (by omega) s hs
  rwa [cornerPoint_one] at h

/-- The one-dimensional strong facet clause, with no hypothesis left. -/
theorem odo_one_strong_facet_final (M t : ℕ) (hM : 2 ≤ M)
    (ht : (t : ℕ∞) < toppleTime 1 M)
    (y : Site 1) (hy : y 0 = 1)
    (h : odoUnif 1 (2 * M) t y = odoUnif 1 (2 * M) t (y + unit 0) + 1) :
    odoUnif 1 (2 * M) (t + 1) y = odoUnif 1 (2 * M) t y ∧
      odoUnif 1 (2 * M) (t + 1) (y + unit 0) = odoUnif 1 (2 * M) t (y + unit 0) + 1 := by
  refine odo_one_strong_facet_uncond M t hM ht ?_ y hy h
  intro s hs
  have hc := odo_corner_le_of_lt_toppleTime 1 M (by omega) (by omega) s hs
  rwa [cornerPoint_one] at hc

end DimRed
