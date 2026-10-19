/-
Weak facet compatibility with a tail of ones, `base_dimension:weak_compatability` of
the statement labelled `base_dimension` in `dimred-corrected-arxiv.tex`, reduced to the same clause with an EMPTY tail one dimension group down.

The direct route, bounding the head second differences by `j`, is circular: by the Laplacian
identity at a facet point, under the clause's own hypothesis that bound is equivalent to the
conclusion.  The paper's route, at `dimred-corrected-arxiv.tex:981-986`, instead identifies the odometer in
dimension `i+1+j` with the odometer in dimension `i+1` by dimensional reduction and applies
the clause there, where the facet is a single point.
-/
import DimRed.Support.FacetLap
import DimRed.Support.FacetNbr
import DimRed.Support.OneDimWeak

namespace DimRed

open LatticeProb

/-- Weak facet compatibility with a tail of `j` ones, obtained from the same clause
with an EMPTY tail one dimension group down, together with dimensional reduction,
which is the paper's route at `dimred-corrected-arxiv.tex:981-986`. -/
theorem weak_facet_of_lower (M i j : ℕ) (_hM : 2 ≤ M) (t : ℕ) (_ht : 1 ≤ t)
    (x : Fin i → ℤ) (_hx2 : ∀ a, 2 ≤ x a)
    (_hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hred1 : ∀ s : ℕ, odoUnif (i + 1 + j) (2 * M) s (facetPoint x 1 j)
        = odoUnif (i + 1) (2 * M) s (facetPoint x 1 0))
    (hred2 : ∀ s : ℕ, odoUnif (i + 1 + j) (2 * M) s (facetPoint x 2 j)
        = odoUnif (i + 1) (2 * M) s (facetPoint x 2 0))
    (hlower : odoUnif (i + 1) (2 * M) t (facetPoint x 1 0)
          = odoUnif (i + 1) (2 * M) t (facetPoint x 2 0) + 1 →
        odoUnif (i + 1) (2 * M) (t + 1) (facetPoint x 1 0)
          = odoUnif (i + 1) (2 * M) t (facetPoint x 1 0))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  have hlow_eq : odoUnif (i + 1) (2 * M) t (facetPoint x 1 0) = odoUnif (i + 1) (2 * M) t (facetPoint x 2 0) + 1 := by
    calc
      odoUnif (i + 1) (2 * M) t (facetPoint x 1 0) = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
        symm; exact hred1 t
      _ = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 := h
      _ = odoUnif (i + 1) (2 * M) t (facetPoint x 2 0) + 1 := by rw [hred2 t]
  have hlow_succ : odoUnif (i + 1) (2 * M) (t + 1) (facetPoint x 1 0) = odoUnif (i + 1) (2 * M) t (facetPoint x 1 0) :=
    hlower hlow_eq
  calc
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) = odoUnif (i + 1) (2 * M) (t + 1) (facetPoint x 1 0) := by
      rw [hred1 (t + 1)]
    _ = odoUnif (i + 1) (2 * M) t (facetPoint x 1 0) := hlow_succ
    _ = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by rw [hred1 t]

end DimRed
