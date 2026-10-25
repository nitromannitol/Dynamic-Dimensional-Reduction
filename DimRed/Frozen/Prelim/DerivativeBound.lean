module

/-
Corollary 2.2 of the corrected edition.
`dimred-corrected-arxiv.tex:552-559` (label `cor:derivative_bound`,
"Derivative bound"):

  "Suppose $v_{\infty}(M, \mathbf{1}_{d-1}) \leq k M$ for integer $k \geq 1$.
   Then, for all $1 \leq j \leq d$ and $t \geq 0$ v_t(x) - v_t(x+e_j) \leq k
   x_j."

`k` is fixed before `j`, `t` and `x`, as in the paper. `(M, 1_{d-1})` is
`cornerPoint`. `v_∞` is valued in `ℕ∞`, so the hypothesis is an inequality
there. The standing hypothesis of the subsection is that the initial sandpile
is constant (`dimred-corrected-arxiv.tex`, label `subsec:derivative_comparison`), carried here as `c`.
-/
public import DimRed.Support.DerivativeBoundFull

@[expose] public section

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.derivative_bound (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (k : ℕ) (hk : 1 ≤ k)
    (hcorner : odoInf d (2 * M) (fun _ => c) (cornerPoint d M) ≤ ((k * M : ℕ) : ℕ∞))
    (j : Fin d) (t : ℕ) (x : Site d) (hx : inSimplex d M x) :
    odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + unit j)
      ≤ (k : ℤ) * x j
-- FROZEN-STATEMENT-END
:= DimRed.Corrected.derivative_bound d M hd c k hk hcorner j t x hx
