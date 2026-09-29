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

/-- The `-e_a` half of the head-coordinate neighbour sum at the facet point
`(x, 1, 1_j)`: the sum is at most `i · v(x,1_j) + ∑_a (x_a - 1)`, from the
first-difference bound at each `x - e_a`. -/
theorem facet_head_minus_sum {i j M : ℕ} (hM : 1 ≤ M) (t : ℕ) (x : Fin i → ℤ)
    (hx2 : ∀ a, 2 ≤ x a) :
    (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j))
      ≤ (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        + ∑ a : Fin i, (x a - 1) := by
  have hd1 : 1 ≤ i + 1 + j := by omega
  have hterm : ∀ a : Fin i,
      odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j)
        ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) + (x a - 1) := by
    intro a
    have hfd := odo_first_diff (i + 1 + j) M hd1 hM t
      (Fin.castAdd j (Fin.castSucc a)) (facetPoint (x - unit a) 1 j)
      (by rw [facetPoint_head (x - unit a) 1 a]
          have hxa := hx2 a
          have hsub : (x - unit a) a = x a - 1 := sub_unit_self i x a
          omega)
    rw [facetPoint_add_head (x - unit a) a] at hfd
    have hx' : x - unit a + unit a = x := by
      ext m
      by_cases hm : m = a
      · rw [hm, add_unit_self i (x - unit a) a, sub_unit_self i x a]
        ring
      · rw [add_unit_other i (x - unit a) a m hm]
        rw [sub_unit_other i x a m hm]
    rw [hx'] at hfd
    have hsub : (x - unit a) a = x a - 1 := sub_unit_self i x a
    rw [facetPoint_head (x - unit a) 1 a, hsub] at hfd
    linarith
  calc (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j))
      ≤ ∑ a : Fin i, (odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) + (x a - 1)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        + ∑ a : Fin i, (x a - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]

end DimRed
