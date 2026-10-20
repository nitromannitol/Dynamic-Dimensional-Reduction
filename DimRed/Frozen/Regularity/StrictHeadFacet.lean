/-
Lemma 5.1 of the corrected edition.
`dimred-corrected-arxiv.tex:1218-1228` (label `lem:strict-head-facet`):

  "Let $d\geq1$, $M\geq2$, $P_M=\{1,\ldots,M\}^d$, and $s_0\equiv2d$. For
   every $t\geq0$, $x\in P_M$ and coordinate $k$ with $x_k<\max_l x_l$,
   v_t(x)-v_t(x+2e_k)\leq2x_k.

  If $x_k=1$, $\max_l x_l\geq2$, and $v_t(x)=v_t(x+e_k)+1$, then
   v_{t+1}(x)=v_t(x),\qquad v_{t+1}(x+e_k)=v_t(x+e_k)+1."

This unit records the constant-two facet bound on a nonempty head and the two
firing conclusions at a unit gap, both for every time `t`.
-/
import DimRed.Support.Case2Closed

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.strict_head_facet
    (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) :
    (∀ (k : Fin d) (x : Site d), case2Pos d M x →
      (∃ l : Fin d, x k < x l) →
      odoUnif d (2 * M) t x -
        odoUnif d (2 * M) t (x + unit k + unit k) ≤ 2 * x k) ∧
    (∀ (k : Fin d) (x : Site d), case2Pos d M x →
      x k = 1 → (∃ l : Fin d, 2 ≤ x l) →
      odoUnif d (2 * M) t x =
        odoUnif d (2 * M) t (x + unit k) + 1 →
      odoUnif d (2 * M) (t + 1) x = odoUnif d (2 * M) t x ∧
      odoUnif d (2 * M) (t + 1) (x + unit k) =
        odoUnif d (2 * M) t (x + unit k) + 1)
-- FROZEN-STATEMENT-END
:= case2_odo_strict_head_and_compat d M t hd hM
