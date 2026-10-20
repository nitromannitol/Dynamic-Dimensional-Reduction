/-
The first display of Theorem 1.1(i) of the corrected edition. `dimred-corrected-arxiv.tex:109-118` (label `the_theorem`), clause 1:

  "Let $N \geq 1$, $d \geq 2$, and $M = \lceil N/2 \rceil$. Denote the
   fundamental domain of $\mathcal{C}_N^{(d)}$ consisting of sorted
   coordinates in decreasing order by $\mathcal{S}^{(d)}_M := \{ (x_1, \ldots,
   x_d): M \geq x_1 \geq \cdots \geq x_d \geq 1 \}$.

  \item{Dimensional reduction:} for all $t \geq 1$ and $\mathbf{x}_{d-1} \in
   \mathcal{S}_M^{(d-1)}$ v_t^{(d, N)}(\mathbf{x}_{d-1}, 1) = v_t^{(d-1,
   N)}(\mathbf{x}_{d-1})"

The dimension is written `d + 1` in place of `d`, so `d ≥ 2` becomes `d ≥ 1`
and `d - 1` needs no truncated subtraction. The initial condition is
`s_0^{(d)} ≡ 2d` in each dimension separately
(`dimred-corrected-arxiv.tex`, label `subsec:overview`), which is what `odoUnif` carries. `(x_{d-1},
1)` appends a last coordinate equal to `1`.
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x
-- FROZEN-STATEMENT-END
:= dimensional_reduction_of_reg reg_proved N d hN hd t ht x hx
