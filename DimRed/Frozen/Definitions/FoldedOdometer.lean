/-
Symmetrized-odometer definition of the corrected edition.
`dimred-corrected-arxiv.tex:380-389` (literal initial value and threshold
recursion; context `subsec:symmetry`):

  "The sum retains all $2d$ directed occurrences, including repeated orbit
   representatives and zero contributions from exterior neighbors. Define the
   symmetrized odometer independently by $v_0^{\mathcal S}\equiv0$ and
   v_{t+1}^{\mathcal S}(x)=v_t^{\mathcal S}(x)+ 1\{s_0(x)+R v_t^{\mathcal
   S}(x)-2d v_t^{\mathcal S}(x)\geq2d\}.

  This uses the physical cube embedding for each parity of $N$: reflection
   sends $0$ to $1$ for even $N$ and $0$ to $2$ for odd $N$."

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
