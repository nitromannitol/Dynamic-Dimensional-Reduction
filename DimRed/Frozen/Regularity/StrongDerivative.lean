/-
The strong derivative clause of Proposition 4.1 of the corrected edition. `dimred-corrected-arxiv.tex:743-745` (label `base_dimension`,
display `base_dimension:strong_derivative`):

  "\item[Strong facet compatibility] Let $i,j\geq0$, $i+1+j=d$, and put
   $p=(\mathbf{x}_i,1,\mathbf{1}_j)\in\mathcal S_M^{(d)}$ with
   $\mathbf{x}_i\geq2$. If $t<\tau_M$, or if $i\geq1$ and $t\geq\tau_M$, then
   v_t^{(M)}(p)-v_t^{(M)}(p+2e_{i+1})\leq2"

`p = (x_i, 1, 1_j)` is defined in the statement (line 740), so `p + 2 e_{i+1}`
is `(x_i, 3, 1_j)`, and `i < d` is automatic once `d = i + 1 + j`. `τ_M` is
`toppleTime d M`, valued in `ℕ∞`. For a nonempty head the corrected edition
states the same bound, at every time, as the first conclusion of
`lem:strict-head-facet` (`dimred-corrected-arxiv.tex:1127-1132`, with `x_k =
1`).
-/
import DimRed.Support.RegProved

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
:= base_dimension_strong_derivative_of_reg reg_proved M i j hM t x hx2 hxs hreg
