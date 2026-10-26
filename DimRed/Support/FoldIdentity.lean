module

public import DimRed.Support.Fundamental
public import DimRed.Support.SimplexFold
public import DimRed.Support.AxisStep

@[expose] public section

open LatticeProb DimRed

namespace DimRed

/-- For a point of the cube with every coordinate at least one, the folding
`foldPoint` is the identity: no reflection is needed. -/
theorem foldPoint_eq_self (d M : ℕ) (z : Site d) (hz : ∀ k, 1 ≤ z k) :
    foldPoint d (2 * M) z = z := by
  funext k
  rw [foldPoint_apply, ite_eq_left (hz k)]

/-- For a point of the cube with every coordinate at least one, the sorted
representative `toSimplexPoint` is the point permuted by `Tuple.sort`. -/
theorem toSimplexPoint_eq_sort (d M : ℕ) (z : Site d) (hz : ∀ k, 1 ≤ z k) :
    toSimplexPoint d M z = fun k => z (Tuple.sort (fun i => -(z i)) k) := by
  funext k
  rw [toSimplexPoint, foldPoint_eq_self d M z hz]

/-- The odometer at the smaller scale is invariant under the fold at the larger
scale, for a point with every coordinate at least one. -/
theorem odoUnif_toSimplexPoint_sub (d m t : ℕ) (z : Site d) (hz : ∀ k, 1 ≤ z k) :
    odoUnif d (2 * (m - 1)) t (fun k => toSimplexPoint d m z k - 1)
      = odoUnif d (2 * (m - 1)) t (fun k => z k - 1) := by
  rw [toSimplexPoint_eq_sort d m z hz]
  -- permutation invariance of the odometer, from `odo_cubeSym`
  have h := odo_cubeSym d (2 * (m - 1)) (fun _ => 2 * (d : ℤ))
    (isSymmetricPile_const' d (2 * (m - 1)) (2 * (d : ℤ))) t
    (Tuple.sort (fun i => -(z i))) (fun _ => true) (fun j => z j - 1)
  have he : cubeSym d (2 * (m - 1)) (Tuple.sort (fun i => -(z i))) (fun _ => true)
      (fun j => z j - 1)
      = fun k => (fun j => z j - 1) (Tuple.sort (fun i => -(z i)) k) := by
    funext k
    simp [cubeSym]
  rw [he] at h
  simpa only [odoUnif] using h

end DimRed
