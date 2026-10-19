/-
Lifted-value definition of the corrected edition.
`dimred-corrected-arxiv.tex:370-377` (literal lifted-value definition; context
`subsec:symmetry`):

  "Let $s_0:\mathcal{C}_N^{(d)}\to\mathbb Z$ be invariant under the cube
   symmetries on its cube domain. Every site $y$ in the cube has a unique
   orbit representative $r_N(y)\in\mathcal{S}^{(d)}_M$; the symmetry taking
   $y$ to that representative need not be unique. For
   $u:\mathcal{S}^{(d)}_M\to\mathbb Z$ define its lifted values by \widetilde
   u(y)=\begin{cases}u(r_N(y)),&y\in\mathcal{C}_N^{(d)},\\
   0,&y\notin\mathcal{C}_N^{(d)}.\end{cases}"

This unit records the lifted value of a function on the fundamental domain as
its value at the orbit representative inside the cube and zero outside it.
-/
import DimRed.Support.ReflectedThreshold

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.folded_lift_definition (d N : ℕ) (v : Corrected.SimplexSite d (sideHalf N) → ℤ) (y : Site d) :
    Corrected.foldedLift d N v y =
      if hy : inCube d N y then
        v ⟨toSimplexPointN d N y, inSimplex_toSimplexPointN d N y hy⟩ else 0
-- FROZEN-STATEMENT-END
:= rfl
