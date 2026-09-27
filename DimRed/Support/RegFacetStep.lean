/-
Strong facet compatibility at one triple, `dimred.tex:1261-1320`, by strong
induction on the time.

The paper's argument: suppose `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1`.  By
strong facet compatibility at `(t-1) → t`, `Δ v_{t-1}(x_i, 1, 1_j) ≥ 0`, so it
suffices to compare the two Laplacians term by term.  The terms come from strong
facet compatibility at time `t-1`, which the strong induction on `t` supplies —
this is what removes the apparent circularity of consuming the clause at the same
triple.

The first-difference part of the clause is Corollary 2.2 at the mid coordinate.
-/
import DimRed.Support.RegFacetTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace DimRed

open LatticeProb

/-- The three term bounds of the paper's Laplacian comparison
(`dimred.tex:1293-1300`), each supplied by strong facet compatibility at time
`t-1`:

* the head terms at time `t` dominate those at time `t-1` (the paper's
  `eq:laplace_11 ≥ eq:laplace_21`);
* the mid term at time `t-1` is at most the mid term at time `t`
  (`eq:laplace_12 ≥ eq:laplace_22`);
* the tail term at time `t-1` is at most the tail term at time `t`
  (`eq:laplace_13 ≥ eq:laplace_23`). -/
structure FacetTermBounds (i j M t : ℕ) (y : Fin i → ℤ) : Prop where
  head : (∑ a : Fin i,
      (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j) +
        odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j)))
    ≤ (∑ a : Fin i,
      (odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) +
        odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j)))
  mid : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
    = odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j)
  tail : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j)
    ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j)
  /-- the gap at time `t-1`, which the clause supplies in the toppling case -/
  gap : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
    = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) + 1
  /-- the two-step bound at time `t`, `eq:two_derivative_bound` -/
  two : odoUnif (i + 1 + j) (2 * M) t (facetPoint y 1 j)
    - odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j) ≤ 2
  /-- the tail term at time `t` is at most the mid term plus one, which is the
  first-difference bound at the mid coordinate -/
  tailstep : odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j)
    - odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j) ≤ 1

/-- The Laplacian at the facet point `(y, 1, 1_j)` is at most the Laplacian at
`(y, 2, 1_j)` when the clause holds at the previous time and the two-step bound
holds at the current time.  This is the paper's comparison of
`eq:laplace_11`–`eq:laplace_13` with `eq:laplace_21`–`eq:laplace_23`. -/
theorem lap_facet_le_of_prev {i j M t : ℕ} (_ht : 1 ≤ t) (_hi : 1 ≤ i) (_hM : 2 ≤ M)
    (_hS : RegStrongFacet (i + 1 + j) M (t - 1))
    (_hderiv : RegStrongDeriv (i + 1 + j) M t)
    (y : Fin i → ℤ) (_hy2 : ∀ a, 2 ≤ y a)
    (_hys : inSimplex (i + 1 + j) M (facetPoint y 1 j))
    (_hys2 : inSimplex (i + 1 + j) M (facetPoint y 2 j))
    (hb : FacetTermBounds i j M t y)
    (hlap2 : lap (odoUnif (i + 1 + j) (2 * M) t) (facetPoint y 2 j)
      = (∑ a : Fin i,
          (odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) +
            odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j))) -
        2 * (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) +
        ((j : ℤ) + 1) *
          (odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j) -
            odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j)))
    (hgap : odoUnif (i + 1 + j) (2 * M) t (facetPoint y 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) + 1) :
    lap (odoUnif (i + 1 + j) (2 * M) (t - 1)) (facetPoint y 1 j)
      ≤ lap (odoUnif (i + 1 + j) (2 * M) t) (facetPoint y 2 j) := by
  -- the two-step bound at the head coordinates
  have htwo := hb.two
  have hhead := hb.head
  -- the mid and tail terms
  have hmid := hb.mid
  have htail := hb.tail
  -- the two Laplacians, in the paper's decomposition
  have hlap1 : lap (odoUnif (i + 1 + j) (2 * M) (t - 1)) (facetPoint y 1 j)
      = (∑ a : Fin i,
          (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j) +
            odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j))) -
        2 * (i : ℤ) * odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j) +
        ((j : ℤ) + 1) *
          (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) -
            odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)) := by
    have h := lap_facetPoint_of (i := i) (j := j) (M := M)
      (2 * ((i + 1 + j : ℕ) : ℤ)) y (t - 1)
    simp only [odoUnif]
    exact h
  rw [hlap1]
  rw [hlap2]
  have hmid1 : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j)
      - odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j) = -1 := by
    linarith [hb.gap]
  have hmid2 : -1 ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) := by
    linarith [hgap, htwo]
  have hj1 : (0 : ℤ) ≤ (j : ℤ) + 1 := by positivity
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  nlinarith [hb.head, hb.mid, hb.tail, hmid1, hmid2, hj1, hi0]

end DimRed
