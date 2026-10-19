/-
Theorem 1.1(ii) of the corrected arXiv-format draft, frozen.
`dimred-corrected-arxiv.tex:122-133` (label `the_theorem`), clause 2:

  "\item{Self-similarity:} for all $j < M$, $t \leq \tau_j$, and $\mathbf{x}
   \in \mathcal{S}_M^{(d)}$ with $\mathbf{x} > M-j$ v_t^{(d, N)}(\mathbf{x}) =
   v_t^{(d, 2 j)}(\mathbf{x}-(M-j)),

  where \tau_{j} := \min\{ t \geq 1: v_t^{(d,2 j)}(\mathbf{x}) \geq j \mbox{
   for some $\mathbf{x}\in\partial\mathcal{C}^{(d)}_{2j}$}\},
   \qquad(\min\varnothing:=+\infty).

  and $\partial \mathcal{C}^{(d)}_i := \{ \mathbf{x} \in \mathcal{C}^{(d)}_i :
   \mbox{there is $\mathbf{y} \not \in \mathcal{C}^{(d)}_i$ with
   $|\mathbf{y}-\mathbf{x|} = 1$}\}$ denotes the inner boundary of the cube."

`τ_j` is `toppleTime d j`, an `sInf` in `ℕ∞`, so `t ≤ τ_j` is an inequality
there. Vector inequalities and the subtraction of a scalar from a vector are
coordinatewise (`dimred-corrected-arxiv.tex:275`).
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    odoUnif d N t x = odoUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ)))
-- FROZEN-STATEMENT-END
:= self_similarity_of_reg reg_proved N d hN hd j hj t ht x hx hxgt
