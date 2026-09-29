import DimRed.Support.FacetLap
import DimRed.Support.AxisStep
import DimRed.Support.FacetNbr
import DimRed.Support.StrongDerivPure
open LatticeProb DimRed
namespace DimRed

/-- The `+e_a` half of the head-coordinate neighbour sum at the facet point
`(x, 1, 1_j)`: each neighbour is at most the point itself, by reflection. -/
theorem facet_head_plus_sum {i j M : ℕ} (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a) :
    (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j))
      ≤ (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  have hterm : ∀ a : Fin i,
      odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j)
        ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
    intro a
    have h := odo_axis_refl (d := i + 1 + j) (M := M) (by omega)
      (2 * ((i + 1 + j : ℕ) : ℤ)) (by positivity) (by omega) t
      (facetPoint x 1 j) (Fin.castAdd j (Fin.castSucc a))
      (by rw [facetPoint_head x 1 a]; exact le_trans (by norm_num) (hx2 a))
    rwa [facetPoint_add_head x a] at h
  calc (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j))
      ≤ ∑ _a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
        simp [Finset.sum_const, Finset.card_univ]

end DimRed
