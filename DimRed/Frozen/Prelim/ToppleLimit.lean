/-
Lemma 2.5 of the corrected edition.
`dimred-corrected-arxiv.tex:561-568` (label `topple_limit`):

  "For all $t \geq t_0$ and $j \geq 0$, \max_{z \in \mathcal{S}} \left(
   v_{t+j}(z) - v_t(z) \right) \leq \max_{z \in \mathcal{S}} \left(
   v_{t_0+j}(z) - v_{t_0}(z) \right)"

`\mathcal{S}` is `S_M^{(d)}`, the sorted fundamental domain of `C_{2M}^{(d)}`,
and `v_t` on it is the odometer of the hypercube (`symmetry_lemma`; see
CORRESPONDENCE.md). The standing symmetry of the initial sandpile
(`dimred-corrected-arxiv.tex:370`) is carried as `hsym`, without which the
maximum over a fundamental domain says nothing about the rest of the cube. The
bound `s_0 ≤ 2(2d) - 1` of `dimred-corrected-arxiv.tex:290` is not a
hypothesis of this statement.
-/
import DimRed.Support.ToppleContractionFull

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.topple_limit (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s₀ : Site d → ℤ)
    (hsym : Corrected.CubeSymmetric d (2 * M) s₀) (t₀ t j : ℕ) (ht : t₀ ≤ t) :
    Corrected.maximum d M (Corrected.simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t + j) z - odo d (2 * M) s₀ t z) ≤
      Corrected.maximum d M (Corrected.simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
-- FROZEN-STATEMENT-END
:= Corrected.topple_limit d M hd hM s₀ hsym t₀ t j ht
