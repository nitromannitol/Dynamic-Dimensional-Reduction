/-
Derivative clause of the one-dimensional terminal lemma (Lemma 4.1) of the
corrected arXiv-format draft, frozen. `dimred-corrected-arxiv.tex:920-927`
(label `lem:one-terminal-profile`, clause full derivative including endpoint):

  "In dimension one, with $s_0\equiv2$ and $1\leq x\leq M$,
   v_\infty(x)-v_\infty(x+1)=x, where $v_\infty(M+1)=0$ is the dissipating
   boundary value."

This unit records the terminal derivative `v_∞(x) - v_∞(x+1) = x` for `1 ≤ x ≤
M`, with `v_∞(M+1) = 0` the exterior value, as a difference of `toNat` values
of `odoInfUnif`.
-/
import DimRed.Support.OneDimTerminalEndpoint

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.one_terminal_derivative (M : ℕ) (hM : 1 ≤ M)
    (x : Site 1) (hx1 : 1 ≤ x 0) (hxM : x 0 ≤ (M : ℤ)) :
    ((odoInfUnif 1 (2 * M) x).toNat : ℤ) -
      ((odoInfUnif 1 (2 * M) (x + unit (0 : Fin 1))).toNat : ℤ) = x 0
-- FROZEN-STATEMENT-END
:= Corrected.one_terminal_derivative M hM x hx1 hxM
