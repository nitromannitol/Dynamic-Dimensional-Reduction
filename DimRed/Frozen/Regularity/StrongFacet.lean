/-
The strong facet compatibility clause of Proposition 4.1 of the corrected edition. `dimred-corrected-arxiv.tex:833-841` (label
`base_dimension`, display `base_dimension:strong_compatability`):

  "\item[Strong facet compatibility] Let $i,j\geq0$, $i+1+j=d$, and put
   $p=(\mathbf{x}_i,1,\mathbf{1}_j)\in\mathcal S_M^{(d)}$ with
   $\mathbf{x}_i\geq2$. If $t<\tau_M$, or if $i\geq1$ and $t\geq\tau_M$, then

  v_t^{(M)}(\mathbf{x}_i,1,\mathbf{1}_j)
   &=v_t^{(M)}(\mathbf{x}_i,2,\mathbf{1}_j)+1\\ & \implies \\
   v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) &= v_{t}^{(M)}(\mathbf{x}_i,
   1, \mathbf{1}_j) \\ v_{t+1}^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j) &=
   v_{t}^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j)+1."

`(x_i, c, 1_j)` is `facetPoint`, as in the weak clause, and the dimension is
`d = i + 1 + j`.
-/
import DimRed.Support.RegProved

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
:= base_dimension_strong_compatibility_of_reg reg_proved M i j hM t x hx2 hxs hreg h
