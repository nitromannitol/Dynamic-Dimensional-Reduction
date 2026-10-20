import Mathlib
import DimRed.MainTheorems
import DimRedAudit.Regularity.SolutionBasic
import DimRedAudit.Support.RegularityBridge

/-!
# Solution: Regularity (Proposition 4.1)

The challenge module `DimRedAudit/Regularity/Challenge.lean` imports only Mathlib and
states the five clauses with one intentional `sorry` each.  This solution imports the
repository together with `DimRedAudit.Regularity.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statements from the restatements in
`DimRed/MainTheorems.lean` through the bridges in
`DimRedAudit/Support/RegularityBridge.lean`.
-/

namespace DimRed.StatementAudit.Regularity

/-- **Proposition 4.1** (`base_dimension`), self-similarity clause (`dimred-corrected-arxiv.tex`, label `base_dimension:consistency`):
for `M ≥ 2`, `1 ≤ j ≤ M`, `t ≤ τ_j` and `x ∈ S_M` with `x > M - j`,
`v_t^{(M)}(x) = v_t^{(j)}(x - (M - j))`. -/
theorem base_dimension_consistency (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ M) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d M x) (hxgt : ∀ i, (M : ℤ) - (j : ℤ) < x i) :
    odoUnif d (2 * M) t x = odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
  rw [Bridge.toppleTime_eq] at ht
  simp only [Bridge.odoUnif_eq]
  exact DimRed.base_dimension_consistency d M hd hM j hj1 hj2 t ht x hx hxgt

/-- **Proposition 4.1** (`base_dimension`), weak facet compatibility (`dimred-corrected-arxiv.tex`, label `base_dimension:weak_compatability`):
if `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1` then `v_{t+1}(x_i, 1, 1_j) = v_t(x_i, 1, 1_j)`. -/
theorem base_dimension_weak_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  simp only [Bridge.odoUnif_eq] at h ⊢
  exact DimRed.base_dimension_weak_compatibility M i j hM t ht x hx2 hxs h

/-- **Proposition 4.1** (`base_dimension`), strong derivative bound (`dimred-corrected-arxiv.tex`, label `base_dimension:strong_derivative`):
for `x_i ≥ 2`, `j ≥ 0` and the regime `t < τ_M` or `i ≥ 1, t ≥ τ_M`,
`v_t(x_i, 1, 1_j) - v_t(x_i, 3, 1_j) ≤ 2`. -/
theorem base_dimension_strong_derivative (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2 := by
  rw [Bridge.toppleTime_eq] at hreg
  simp only [Bridge.odoUnif_eq]
  exact DimRed.base_dimension_strong_derivative M i j hM t x hx2 hxs hreg

/-- **Proposition 4.1** (`base_dimension`), strong facet compatibility (`dimred-corrected-arxiv.tex`, label `base_dimension:strong_compatability`):
under the derivative bound's hypotheses and the gap
`v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1`, the first point stays and the second topples. -/
theorem base_dimension_strong_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 := by
  rw [Bridge.toppleTime_eq] at hreg
  simp only [Bridge.odoUnif_eq] at h ⊢
  exact DimRed.base_dimension_strong_compatibility M i j hM t x hx2 hxs hreg h

/-- **Proposition 4.1** (`base_dimension`), strong topple control (`dimred-corrected-arxiv.tex`, label `base_dimension:strong_topple`):
for all `t ≥ τ_{M-1}`, `sup_{x ∈ S_M}(v_{t+2}(x) - v_t(x)) ≤ 1`. -/
theorem base_dimension_strong_topple (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    simplexMax d M (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1 := by
  rw [Bridge.toppleTime_eq] at ht
  simp only [Bridge.simplexMax_eq, Bridge.odoUnif_eq]
  rw [← DimRed.Corrected.maximum_eq_simplexMax d M
    (DimRed.Corrected.simplexNonempty d M (by omega))]
  exact DimRed.base_dimension_strong_topple d M hd hM t ht

end DimRed.StatementAudit.Regularity
