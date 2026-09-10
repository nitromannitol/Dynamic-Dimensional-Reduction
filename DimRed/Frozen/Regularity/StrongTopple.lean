/-
The strong topple control clause of Proposition 4.1 of `dimred.tex`, frozen.
`dimred.tex:946-950` (display `base_dimension:strong_topple`):

  "[Strong topple control] For all $t \geq \tau_{M-1}$,
   $\sup_{\mathbf{x} \in \mathcal{S}_M} (v_{t+2}(\mathbf{x}) -
   v_{t}(\mathbf{x})) \leq 1$."

`τ_{M-1}` is `toppleTime d (M-1)`, valued in `ℕ∞`.  The supremum over the
finite domain is `simplexMax`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_dimension_strong_topple (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    simplexMax d M (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1
-- FROZEN-STATEMENT-END
:= by sorry
