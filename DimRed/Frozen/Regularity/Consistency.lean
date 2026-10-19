/-
The self-similarity clause of Proposition 4.1 of the corrected arXiv-format
draft, frozen. `dimred-corrected-arxiv.tex:727-729` (label `base_dimension`,
display `base_dimension:consistency`):

  "Recall the definition of $\tau_{j}$ from Theorem \ref{the_theorem}. For all
   $M \geq 2$ and $d \geq 1$, the odometer maintains the following properties
   throughout the parallel toppling process.

  \item[Self-similarity] For each $1 \leq j \leq M$ and $t \leq \tau_j$
   v_t^{(M)}(\mathbf{x}) = v_t^{(j)}(\mathbf{x}-(M-j)) \mbox{ for $\mathbf{x}
   > M-j$}."

`v_t^{(M)}` is the odometer of the initial condition `s_0 ≡ 2d`
(`dimred-corrected-arxiv.tex:38`) on the hypercube `C_{2M}^{(d)}`, restricted
to `S_M^{(d)}` (`dimred-corrected-arxiv.tex:420-422`). `τ_j` is `toppleTime`;
it is valued in `ℕ∞`, so `t ≤ τ_j` is an inequality there. Vector inequalities
are coordinatewise (`dimred-corrected-arxiv.tex:275`).
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_consistency (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ M) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d M x) (hxgt : ∀ i, (M : ℤ) - (j : ℤ) < x i) :
    odoUnif d (2 * M) t x = odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ)))
-- FROZEN-STATEMENT-END
:= base_dimension_consistency_of_reg reg_proved d M hd hM j hj1 hj2 t ht x hx hxgt
