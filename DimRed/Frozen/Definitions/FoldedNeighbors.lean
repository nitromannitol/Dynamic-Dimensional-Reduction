/-
Directed-neighbour definition of the corrected edition.
`dimred-corrected-arxiv.tex:378-380` (literal directed-neighbor definition;
context `subsec:symmetry`):

  "Write $R u(x)=\sum_{i=1}^d(\widetilde u(x+e_i)+\widetilde u(x-e_i))$. The
   sum retains all $2d$ directed occurrences, including repeated orbit
   representatives and zero contributions from exterior neighbors. Define"

This unit records the directed-neighbour sum of the lifted values over all
`2d` occurrences, with repeated representatives and exterior zeros kept.
-/
import DimRed.Support.ReflectedThreshold

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.folded_neighbors_definition (d N : ℕ) (v : Corrected.SimplexSite d (sideHalf N) → ℤ)
    (x : Corrected.SimplexSite d (sideHalf N)) :
    Corrected.foldedNbrSum d N v x =
      ∑ i : Fin d, (Corrected.foldedLift d N v (x.val + unit i) +
        Corrected.foldedLift d N v (x.val - unit i))
-- FROZEN-STATEMENT-END
:= rfl
