/-
Lifted-value definition of the corrected edition.
`dimred-corrected-arxiv.tex:371-374` (literal lifted-value definition; context
`subsec:symmetry`):

  "Let $s_0:\mathcal{C}_N^{(d)}\to\Z$ be symmetric, that is, $\sigma s_0=s_0$
   for every $\sigma\in\operatorname{Aut}_{\mathcal{C}_d}$. Every site
   $y\in\mathcal{C}_N^{(d)}$ has exactly one point $r_N(y)\in\mathcal{S}^{(d)}_M$
   in its orbit under $\operatorname{Aut}_{\mathcal{C}_d}$, although the
   symmetry carrying $y$ to $r_N(y)$ need not be unique. Here a reflection of
   one coordinate exchanges $0$ and $1$ when $N$ is even, and $0$ and $2$ when
   $N$ is odd, in the coordinates of $\mathcal{C}_N^{(d)}$ fixed above. For
   $u:\mathcal{S}^{(d)}_M\to\Z$ define $\widetilde u:\Z^d\to\Z$ by
   \widetilde u(y)=\begin{cases}u(r_N(y)), & y\in\mathcal{C}_N^{(d)},\\ 0, &
   y\notin\mathcal{C}_N^{(d)},\end{cases}"

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
