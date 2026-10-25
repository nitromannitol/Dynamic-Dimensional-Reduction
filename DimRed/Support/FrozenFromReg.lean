module

public import DimRed.Support.RegInduction

@[expose] public section

/-!
# The regularity clauses of Proposition 4.1 from the joint induction

Each theorem below states a frozen regularity clause of Proposition 4.1 (the statement labelled `base_dimension` in `dimred-corrected-arxiv.tex`)
verbatim, with the conclusion of the joint induction `reg_all` as its only hypothesis.  The
frozen proofs are then `exact X_of_reg (reg_all ...)`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

open LatticeProb

namespace DimRed

/-- Self-similarity, `base_dimension:consistency`. -/
theorem base_dimension_consistency_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ M) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d M x) (hxgt : ∀ i, (M : ℤ) - (j : ℤ) < x i) :
    odoUnif d (2 * M) t x = odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ))) :=
  (hreg d M t hd hM).1.1 j hj1 hj2 ht x hx hxgt

/-- Weak facet compatibility, `base_dimension:weak_compatability`. -/
theorem base_dimension_weak_compatibility_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) :=
  (hreg (i + 1 + j) M t (by omega) hM).1.2.1 i j rfl ht x hx2 hxs h

/-- Strong derivative compatibility, `base_dimension:strong_derivative`. -/
theorem base_dimension_strong_derivative_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg' : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2 :=
  (hreg (i + 1 + j) M t (by omega) hM).1.2.2.1 i j rfl x hx2 hxs hreg'

/-- Strong facet compatibility, `base_dimension:strong_compatability`. -/
theorem base_dimension_strong_compatibility_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg' : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 :=
  (hreg (i + 1 + j) M t (by omega) hM).1.2.2.2.1 i j rfl x hx2 hxs hreg' h

/-- Strong topple control, `base_dimension:strong_topple`. -/
theorem base_dimension_strong_topple_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    simplexMax d M (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1 :=
  (hreg d M t hd hM).1.2.2.2.2 ht

end DimRed
