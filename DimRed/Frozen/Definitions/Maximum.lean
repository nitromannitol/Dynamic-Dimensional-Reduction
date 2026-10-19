/-
Nonempty-maximum clause of the topple-limit statement in the corrected
arXiv-format draft, frozen. `dimred-corrected-arxiv.tex:561-568` (label
`topple_limit`, the finite maximum over the sorted domain):

  "For all $t \geq t_0$ and $j \geq 0$, \max_{z \in \mathcal{S}} \left(
   v_{t+j}(z) - v_t(z) \right) \leq \max_{z \in \mathcal{S}} \left(
   v_{t_0+j}(z) - v_{t_0}(z) \right)"

This unit records the maximum over the fundamental domain in that statement as
the supremum over the nonempty simplex, `Corrected.maximum`, which takes the
nonemptiness proof as an argument.
-/
import DimRed.Support.SourceCarriers

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.maximum_definition (d M : ℕ) (hne : (simplex d M).Nonempty) (f : Site d → ℤ) :
    Corrected.maximum d M hne f = (simplex d M).sup' hne f
-- FROZEN-STATEMENT-END
:= rfl
