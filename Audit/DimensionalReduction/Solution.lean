import Mathlib
import DimRed.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: DimensionalReduction (Theorem 1.1(i))

The challenge module `Audit/DimensionalReduction/Challenge.lean` imports only Mathlib and
states the theorems with one intentional `sorry` each.  This solution imports the repository
together with `Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statements from `DimRed.dimensional_reduction` and
`DimRed.terminal_dimensional_reduction` (`DimRed/MainTheorems.lean`) through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace DimRed.StatementAudit.DimensionalReduction

/-- **Theorem 1.1(i)** (`the_theorem`, `dimred.tex:114-117`), first display: dimensional
reduction on the centre slice, `v_t^{(d,N)}(x_{d-1}, 1) = v_t^{(d-1,N)}(x_{d-1})` for every
`t ≥ 1` and `x_{d-1} ∈ S_M^{(d-1)}`. -/
theorem dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x := by
  rw [Bridge.odoUnif_eq, Bridge.odoUnif_eq]
  exact DimRed.dimensional_reduction N d hN hd t ht x hx

/-- **Theorem 1.1(i)** (`the_theorem`, `dimred.tex:118-121`), second display: terminal
dimensional reduction, `v_∞^{(d,N)}(x_{d-1}, 2) = v_∞^{(d-1,N)}(x_{d-1})` for
`x_{d-1} ∈ S_M^{(d-1)}` with `x_{d-1} ≥ 2`. -/
theorem terminal_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) N (Fin.snoc x 2) = odoInfUnif d N x := by
  rw [Bridge.odoInfUnif_eq, Bridge.odoInfUnif_eq]
  exact DimRed.terminal_dimensional_reduction N d hN hd x hx hx2

end DimRed.StatementAudit.DimensionalReduction
