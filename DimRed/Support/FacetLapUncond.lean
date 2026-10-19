/-
The Laplacian at a facet point, with no hypotheses.  `DimRed/Support/FacetLap.lean` carries the
five neighbour identities as assumptions because it was proved before them; all five are
theorems of `DimRed/Support/FacetNbr.lean`, so the decomposition of `dimred-corrected-arxiv.tex:962-966` holds
outright.  The only gap between the two files is the way a tail index is written: `FacetLap`
describes it by the inequality `i + 1 ≤ l`, `FacetNbr` by the constructor `Fin.natAdd (i+1)`.
-/
import DimRed.Support.FacetLap
import DimRed.Support.FacetNbr

namespace DimRed

open LatticeProb

/-- A tail index of `Fin (i + 1 + j)` is `Fin.natAdd (i + 1) b` for a unique `b : Fin j`. -/
theorem exists_natAdd_of_isTail {i j : ℕ} (l : Fin (i + 1 + j)) (hl : IsTail l) :
    ∃ b : Fin j, l = Fin.natAdd (i + 1) b := by
  have hlt : (l : ℕ) < i + 1 + j := l.isLt
  have hle : i + 1 ≤ (l : ℕ) := hl
  refine ⟨⟨(l : ℕ) - (i + 1), by omega⟩, ?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

/-- `dimred-corrected-arxiv.tex:962-966` with every hypothesis discharged. -/
theorem lap_facetPoint_of {i j M : ℕ} (c' : ℤ) (x : Fin i → ℤ) (t : ℕ) :
    lap (odo (i + 1 + j) (2 * M) (fun _ => c') t) (facetPoint x 1 j) =
      (∑ a : Fin i,
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x + unit a) 1 j) +
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x - unit a) 1 j))) -
        2 * (i : ℤ) * odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j) +
      ((j : ℤ) + 1) *
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) -
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)) := by
  refine lap_facetPoint c' x t ?_ ?_ ?_ ?_ ?_
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_sub_tail x c' t b
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_add_tail x c' t b
  · exact odo_facetPoint_sub_mid x c' t
  · exact odo_facetPoint_add_mid x c' t
  · intro a
    exact ⟨facetPoint_add_head x a, facetPoint_sub_head x a⟩

/-- At the all-ones point the Laplacian is `d (v_t(2,1_j) - v_t(1,1_j))`,
the weak facet compatibility clause of `dimred-corrected-arxiv.tex`, with `d = j + 1`. -/
theorem lap_facetPoint_zero_of {j M : ℕ} (c' : ℤ) (x : Fin 0 → ℤ) (t : ℕ) :
    lap (odo (0 + 1 + j) (2 * M) (fun _ => c') t) (facetPoint x 1 j) =
      ((j : ℤ) + 1) *
        (odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) -
          odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)) := by
  refine lap_facetPoint_zero c' x t ?_ ?_ ?_ ?_
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_sub_tail x c' t b
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_add_tail x c' t b
  · exact odo_facetPoint_sub_mid x c' t
  · exact odo_facetPoint_add_mid x c' t

/-- Weak facet compatibility at the all-ones point, unconditionally: with a unit facet gap the
site does not fire, because its Laplacian is `-d`.  This is the `i = 0` case of the
weak facet compatibility clause (`base_dimension:weak_compatability`) of `dimred-corrected-arxiv.tex`. -/
theorem odo_succ_facetPoint_zero_of {j M : ℕ} (x : Fin 0 → ℤ) (t : ℕ)
    (hv : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) =
      odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (0 + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) =
      odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  refine odo_succ_facetPoint_zero x t ?_ ?_ ?_ ?_ hv (by omega)
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_sub_tail x _ t b
  · intro l hl
    obtain ⟨b, rfl⟩ := exists_natAdd_of_isTail l hl
    exact odo_facetPoint_add_tail x _ t b
  · exact odo_facetPoint_sub_mid x _ t
  · exact odo_facetPoint_add_mid x _ t

end DimRed
