import DimRed.Support.Recursion
import DimRed.Support.SimplexFold
import DimRed.Support.CornerReaches
import DimRed.Support.ToppleTime

open LatticeProb DimRed

namespace DimRed

/-- The topple time at scale one is one: the corner of the side-`2` cube reaches
one topple at the first step, and no site has toppled before it. -/
theorem toppleTime_one_eq_one (d : ℕ) (hd : 1 ≤ d) : toppleTime d 1 = 1 := by
  refine le_antisymm ?_ (one_le_toppleTime d 1)
  have hhit : ∃ n : ℕ, 1 ≤ n ∧ (1 : ℤ) ≤ odoUnif d (2 * 1) n (cornerPoint d 1) :=
    ⟨1, le_rfl, by simpa using corner_one_le d⟩
  refine (toppleTime_le_iff d 1 hd (by norm_num) hhit (1 : ℕ∞)).mpr ?_
  exact ⟨1, le_rfl, le_rfl, by simpa using corner_one_le d⟩

end DimRed
