import DimRed.Support.RegFacetStep
import DimRed.Support.HeadTermSub

/-!
# The term bounds of the paper's Laplacian comparison

The three term bounds of `dimred.tex:1293-1300`, each supplied by strong facet
compatibility at time `t - 1` and the two-step derivative bound at time `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the term bounds expand two `Finset.sum`s over `Fin i` and their head and tail
-- neighbours, which needs the extra budget
set_option maxHeartbeats 800000

namespace DimRed

open LatticeProb

/-- The head terms at time `t` dominate those at time `t - 1`, in the positive
direction. -/
theorem head_term_add_of (i j M t : ℕ) (ht : 1 ≤ t) (hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : ∀ (i' j' : ℕ), i' + 1 + j' = i + 1 + j → 1 ≤ i' →
      RegStrongFacet (i' + 1 + j') M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∀ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) (a : Fin i) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) :=
  head_term_add i j M t ht hi hM hS y hy2 hys a

/-- The head terms at time `t` dominate those at time `t - 1`, in the negative
direction, whenever the shifted point still has a coordinate at least two. -/
theorem head_term_sub_of (i j M t : ℕ) (ht : 1 ≤ t) (hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : ∀ (i' j' : ℕ), i' + 1 + j' = i + 1 + j → 1 ≤ i' →
      RegStrongFacet (i' + 1 + j') M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∀ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) (a : Fin i)
    (h2 : ∃ l, 2 ≤ (facetPoint (y - unit a) 1 j) l) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j) :=
  head_term_sub i j M t ht hi hM (hS i j rfl hi) y hy2 hys a h2


end DimRed
