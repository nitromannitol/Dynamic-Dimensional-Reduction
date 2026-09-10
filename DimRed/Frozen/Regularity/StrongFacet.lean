/-
The strong facet compatibility clause of Proposition 4.1 of `dimred.tex`,
frozen.  `dimred.tex:935-943` (display `base_dimension:strong_compatability`):

  "For all $\mathbf{x}_i \geq 2$, $j \geq 0$, $i < d$, ($t < \tau_M$ and
   $i \geq 0$) or ($i \geq 1$ and $t \geq \tau_M$),
   $v_t^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) =
    v_t^{(M)}(\mathbf{x}_i, 2, \mathbf{1})+ 1$
   $\implies$
   $v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) =
    v_{t}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j)$ and
   $v_{t+1}^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j) =
    v_{t}^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j)+1$."

The second argument list of the hypothesis is `(x_i, 2, 1_j)`, as everywhere
else in the display and in the proof; the printed `(x_i, 2, 1)` drops the
subscript.  The discrepancy is recorded in the errata.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_strong_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1
-- FROZEN-STATEMENT-END
:= by sorry
