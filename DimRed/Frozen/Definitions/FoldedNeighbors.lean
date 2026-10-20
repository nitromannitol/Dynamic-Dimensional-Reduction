/-
Neighbour-sum definition of the corrected edition.
`dimred-corrected-arxiv.tex:375-379` (literal neighbour-sum definition;
context `subsec:symmetry`):

  "and put, for $x\in\mathcal{S}^{(d)}_M$,
   Ru(x)=\sum_{i=1}^d\big(\widetilde u(x+e_i)+\widetilde u(x-e_i)\big)\,.
   Each of the $2d$ neighbors of $x$ contributes one term to $Ru(x)$: a point
   of $\mathcal{S}^{(d)}_M$ is counted once for each neighbor of $x$ in its
   orbit, and a neighbor outside $\mathcal{C}_N^{(d)}$ contributes zero."

This unit records the sum of the lifted values over the
`2d` neighbours, each orbit point counted with multiplicity and exterior
neighbours contributing zero.
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
