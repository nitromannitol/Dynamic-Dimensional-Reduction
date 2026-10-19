/-
Quadratic-profile clause of the one-dimensional terminal lemma (Lemma 4.1) of
the corrected arXiv-format draft, frozen. `dimred-corrected-arxiv.tex:920-927`
(label `lem:one-terminal-profile`, clause quadratic profile):

  "In dimension one, with $s_0\equiv2$ and $1\leq x\leq M$,
   v_\infty(x)=\frac{M(M+1)-x(x-1)}2,\qquad"

This unit records the terminal profile `v_∞(x) = (M(M+1) - x(x-1))/2` on `1 ≤
x ≤ M`, with integer division and `toNat`, as the value of `odoInfUnif`.
-/
import DimRed.Support.OneDimTerminal

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.one_terminal_profile (M : ℕ) (hM : 1 ≤ M)
    (x : Site 1) (hx1 : 1 ≤ x 0) (hxM : x 0 ≤ (M : ℤ)) :
    odoInfUnif 1 (2 * M) x =
      (((M : ℤ) * ((M : ℤ) + 1) - x 0 * (x 0 - 1)) / 2).toNat
-- FROZEN-STATEMENT-END
:= odoInf_one_eq M hM x hx1 hxM
