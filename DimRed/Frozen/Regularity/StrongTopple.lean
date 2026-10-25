module

/-
The strong topple control clause of Proposition 4.1 of the corrected edition. `dimred-corrected-arxiv.tex:845-847` (label
`base_dimension`, display `base_dimension:strong_topple`):

  "For all $t \geq \tau_{M-1}$, \sup_{\mathbf{x} \in \mathcal{S}_M}
   \left(v_{t+2}(\mathbf{x}) - v_{t}(\mathbf{x})\right) \leq 1."

`τ_{M-1}` is `toppleTime d (M-1)`, valued in `ℕ∞`. The supremum over the
finite domain is `Corrected.maximum`, the nonempty-maximum unit of
`dimred-corrected-arxiv.tex`, label `topple_limit`.
-/
public import DimRed.Support.RegProved
public import DimRed.Support.SourceCarriers

@[expose] public section

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_strong_topple (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    Corrected.maximum d M (Corrected.simplexNonempty d M (by omega)) (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1
-- FROZEN-STATEMENT-END
:= by
  rw [Corrected.maximum_eq_simplexMax]
  exact base_dimension_strong_topple_of_reg reg_proved d M hd hM t ht
