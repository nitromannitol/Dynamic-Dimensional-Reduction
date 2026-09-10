/-
Lemma 2.5 of `dimred.tex`, frozen.  `dimred.tex:669-674` (label `topple_limit`):

  "For all $t \geq t_0$ and $j \geq 0$,
   $\max_{z \in \mathcal{S}} ( v_{t+j}(z) - v_t(z) ) \leq
    \max_{z \in \mathcal{S}} ( v_{t_0+j}(z) - v_{t_0}(z) )$."

`\mathcal{S}` is `S_M^{(d)}`, the sorted fundamental domain of `C_{2M}^{(d)}`,
and `v_t` on it is the odometer of the hypercube (`symmetry_lemma`; see
CORRESPONDENCE.md).  The standing hypothesis of Section 2 on the initial
sandpile is carried as `hs0` and `hs1`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.topple_limit (d M : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, 0 ≤ s₀ y) (hs1 : ∀ y, s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t₀ t j : ℕ) (ht : t₀ ≤ t) :
    simplexMax d M (fun z => odo d (2 * M) s₀ (t + j) z - odo d (2 * M) s₀ t z) ≤
      simplexMax d M (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
-- FROZEN-STATEMENT-END
:= by sorry
