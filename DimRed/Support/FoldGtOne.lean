import DimRed.Support.Fundamental
import DimRed.Support.SimplexFold
import DimRed.Support.AxisStep
import DimRed.Support.BaseDimension

open LatticeProb DimRed

namespace DimRed

/-- A point of the cube whose coordinates are all at least two has a fold in
`S_m` whose coordinates are all above one.  This is the side condition that the
fold route of the one-step self-similarity needs. -/
theorem toSimplexPoint_gt_one (d m : ℕ) (z : Site d) (hz : inCube d (2 * m) z)
    (hz2 : ∀ k : Fin d, 2 ≤ z k) :
    inSimplex d m (toSimplexPoint d m z) ∧
      (∀ k : Fin d, 1 < toSimplexPoint d m z k) := by
  refine ⟨inSimplex_toSimplexPoint d m z hz, fun k => ?_⟩
  have hmem := foldPoint_mem d m z hz k
  rw [toSimplexPoint]
  have hfold2 : 2 ≤ foldPoint d (2 * m) z
      (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k) := by
    rw [foldPoint_apply]
    by_cases h1 : 1 ≤ z (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k)
    · rw [if_pos h1]
      exact hz2 _
    · rw [if_neg h1]
      rw [loCoord_add_hiCoord_two_mul]
      -- unreachable: `hz2` gives `2 ≤ z k` for every `k`
      exact absurd (hz2 (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k)) (by omega)
  linarith

end DimRed
