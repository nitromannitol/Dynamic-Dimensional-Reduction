/-
Symmetrized-odometer definition of the corrected edition.
`dimred-corrected-arxiv.tex:380-384` (literal initial value and threshold
recursion; context `subsec:symmetry`):

  "Each of the $2d$ neighbours of $x$ contributes one term to $Ru(x)$: a point
   of $\mathcal{S}^{(d)}_M$ is counted once for each neighbour of $x$ in its
   orbit, and a neighbour outside $\mathcal{C}_N^{(d)}$ contributes zero. The
   \textbf{symmetrized odometer} is defined by $v_0^{\mathcal S}\equiv0$ and
   v_{t+1}^{\mathcal S}(x)=v_t^{\mathcal S}(x)+\mathbf 1\{s_0(x)+Rv_t^{\mathcal
   S}(x)-2d\,v_t^{\mathcal S}(x)\geq2d\}
   for $x\in\mathcal{S}^{(d)}_M$ and $t\geq0$."

This unit records the symmetrized odometer `foldedOdo` by its zero initial
value and its threshold recursion on the folded neighbour sum.
-/
import DimRed.Support.ReflectedThreshold

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.folded_odometer_definition (d N : ℕ) (s₀ : Site d → ℤ) :
    (∀ x : Corrected.SimplexSite d (sideHalf N), Corrected.foldedOdo d N s₀ 0 x = 0) ∧
    (∀ (t : ℕ) (x : Corrected.SimplexSite d (sideHalf N)),
      Corrected.foldedOdo d N s₀ (t + 1) x = Corrected.foldedOdo d N s₀ t x +
        (if 2 * (d : ℤ) ≤ s₀ x.val +
          Corrected.foldedNbrSum d N (Corrected.foldedOdo d N s₀ t) x -
          2 * (d : ℤ) * Corrected.foldedOdo d N s₀ t x then 1 else 0))
-- FROZEN-STATEMENT-END
:= ⟨fun _ => rfl, fun _ _ => rfl⟩
