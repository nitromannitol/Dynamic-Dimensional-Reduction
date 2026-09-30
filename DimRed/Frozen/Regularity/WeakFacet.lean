/-
The weak facet compatibility clause of Proposition 4.1 of `dimred.tex`, frozen.
`dimred.tex:919-926` (display `base_dimension:weak_compatability`):

  "[Weak facet compatibility] For all $\mathbf{x}_i \geq 2$, $t \geq 1$,
   $i \geq 0$, $j \geq 0$ and $i+j+1=d$,
   $v_t^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) =
    v_t^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j)+ 1$
   $\implies$
   $v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) =
    v_{t}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j)$."

That is, the site does not topple at this step, as the paper's proofs derive
and its applications use: `dimred.tex:1005` ("If $v_t(1) = v_t(2) + 1$, then
$\Delta v_t(1) = -1$ and so $v_{t+1}(1) = v_{t}(1)$"), `dimred.tex:1436-1445`
(the same computation for `d ≥ 2`), and `dimred.tex:1154-1158`, which reads
`v_{t-1}^{(d)}(x_i, 1_{d-i}) = v_t^{(d)}(x_i, 1_{d-i})` off it.

`(x_i, c, 1_j)` is `facetPoint`, and the dimension is `d = i + 1 + j`.
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_weak_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
-- FROZEN-STATEMENT-END
:= base_dimension_weak_compatibility_of_reg reg_proved M i j hM t ht x hx2 hxs h
