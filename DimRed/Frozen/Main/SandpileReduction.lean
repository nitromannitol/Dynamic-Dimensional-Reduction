/-
Corollary to Theorem 1.1 of the corrected arXiv-format draft, frozen.
`dimred-corrected-arxiv.tex:147-154` (label `sandpile_corollary`), clause 1:

  "The results in Theorem \ref{the_theorem}, using the same notation, extend
   to the sequence of sandpiles.

  \item{Dimensional reduction:} for all $\mathbf{x}_{d-1} \in
   \mathcal{S}_M^{(d-1)}$ with $\mathbf{x}_{d-1} \geq 2$
   s_{\infty}^{(d,N)}(\mathbf{x}_{d-1},1) =
   s_{\infty}^{(d-1,N)}(\mathbf{x}_{d-1})+2."

The dimension is written `d + 1` in place of `d`. `s_∞ = 2d + Δ v_∞` is
`Corrected.terminalPile` (the same expression as `sandpInfUnif`), an integer,
with `v_∞` read through `ℕ∞`.
-/
import DimRed.Support.RegProved
import DimRed.Support.SourceCarriers

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.sandpile_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    Corrected.terminalPile (d + 1) N (by omega) (Corrected.cubeSnocOne d N hN x hx) =
      Corrected.terminalPile d N hd (Corrected.cubeSimplexSite d N hN x hx) + 2
-- FROZEN-STATEMENT-END
:= sandpile_dimensional_reduction_of_reg reg_proved N d hN hd x hx hx2
