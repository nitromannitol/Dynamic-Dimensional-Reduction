/-
The strong derivative clause of Proposition 4.1 of `dimred.tex`, frozen.
`dimred.tex:931-934` (display `base_dimension:strong_derivative`):

  "[Strong facet compatibility] For all $\mathbf{x}_i \geq 2$, $j \geq 0$,
   $i < d$, ($t < \tau_M$ and $i \geq 0$) or ($i \geq 1$ and $t \geq \tau_M$),
   $v_t^{(M)}(\mathbf{x}) - v_t^{(M)}(\mathbf{x} + 2 e_{i+1}) \leq 2$."

`x` is the point `(x_i, 1, 1_j)` of the display that follows it, so
`x + 2 e_{i+1}` is `(x_i, 3, 1_j)`; this is how the paper uses it at
`dimred.tex:1256-1258`, `eq:two_derivative_bound`.  `i < d` is automatic once
`d = i + 1 + j`.  `τ_M` is `toppleTime d M`, valued in `ℕ∞`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_strong_derivative (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2
-- FROZEN-STATEMENT-END
:= by sorry
