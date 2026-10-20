/-
Corollary 2.1 of the corrected edition.
`dimred-corrected-arxiv.tex:525-535` (label `axis_monotonicity`, "Axis
monotonicity"), attributed to Babai and Gorodezky:

  "For all $t\geq1$, $x\in\mathcal S$, every $1\leq i\leq d$, and $\mathcal
   J=\varnothing$ or $\mathcal J=\{j\}$ with $i<j\leq d$, v_t(x)\geq
   v_t(x+e_i-e_{\mathcal J}) \quad\mbox{when $x+e_i-e_{\mathcal J}\in\mathcal
   S$}, where $e_{\mathcal J}=\sum_{k\in\mathcal J}e_k$.

  In particular, iteration gives the pure-coordinate monotonicity for any
   sequence of steps away from reflection mirrors."

One index up and at most one index down is the statement of the source the
corollary cites. Babai and Gorodezky's Definition 5.2 calls `f` axis monotone
when `f(r) ≤ f(s)` for each pair of lattice points with `s - r` perpendicular
to one axis of symmetry of `f` and `s` closer to that axis than `r`: one step,
perpendicular to one axis. On `S_M^{(d)}` the axes of symmetry are the
reflections `x_i = 1/2`, whose perpendicular step is `e_i`, and the rotations
`x_i = x_j`, whose perpendicular step is `e_i - e_j` with `i < j`. Those are
the two moves below. The use in Section 5 of the corrected edition
(`dimred-corrected-arxiv.tex`, label `subsubsec:higher_strong_topple`) is a chain of the moves stated here. The
standing hypothesis of the subsection is that the initial sandpile is constant
(`dimred-corrected-arxiv.tex`, label `subsec:derivative_comparison`), carried here as `c`. The paper's `t ≥
1` is carried too, although the proof does not need it: at `t = 0` both sides
are zero.
-/
import DimRed.Support.AxisMonotonicityFull

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.axis_monotonicity (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (t : ℕ) (_ht : 1 ≤ t) (x : Site d) (hx : inSimplex d M x)
    (i : Fin d) (J : Finset (Fin d)) (hJ : J.card ≤ 1) (hiJ : ∀ j ∈ J, i < j)
    (hmem : inSimplex d M (x + unit i - ∑ j ∈ J, unit j)) :
    odo d (2 * M) (fun _ => c) t (x + unit i - ∑ j ∈ J, unit j)
      ≤ odo d (2 * M) (fun _ => c) t x
-- FROZEN-STATEMENT-END
:= DimRed.Corrected.axis_monotonicity d M hd c t _ht x hx i J hJ hiJ hmem
