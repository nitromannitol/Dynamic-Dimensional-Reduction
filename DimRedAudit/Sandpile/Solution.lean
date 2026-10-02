import Mathlib
import DimRed.MainTheorems
import DimRedAudit.Sandpile.SolutionBasic
import DimRedAudit.Support.SandpileBridge

/-!
# Solution: Sandpile (Corollary 1.1)

The challenge module `DimRedAudit/Sandpile/Challenge.lean` imports only Mathlib and states
the theorems with one intentional `sorry` each.  This solution imports the repository together
with `DimRedAudit.Sandpile.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statements from `DimRed.sandpile_dimensional_reduction` and
`DimRed.sandpile_self_similarity` (`DimRed/MainTheorems.lean`) through the bridges in
`DimRedAudit/Support/SandpileBridge.lean`.
-/

namespace DimRed.StatementAudit.Sandpile

/-- **Corollary 1.1(i)** (`sandpile_corollary`, `dimred.tex:149-152`): dimensional reduction
of the terminal sandpile, `s_∞^{(d,N)}(x_{d-1}, 1) = s_∞^{(d-1,N)}(x_{d-1}) + 2` for
`x_{d-1} ∈ S_M^{(d-1)}` with `x_{d-1} ≥ 2`. -/
theorem sandpile_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    sandpInfUnif (d + 1) N (Fin.snoc x 1) = sandpInfUnif d N x + 2 := by
  rw [Bridge.sandpInfUnif_eq, Bridge.sandpInfUnif_eq]
  exact DimRed.sandpile_dimensional_reduction N d hN hd x hx hx2

/-- **Corollary 1.1(ii)** (`sandpile_corollary`, `dimred.tex:153-156`): self-similarity of
the sandpile, for all `j < M`, `t ≤ τ_j` and `x ∈ S_M^{(d)}` with `x > M - j + 1`,
`s_t^{(d,N)}(x) = s_t^{(d,2j)}(x - (M - j))`. -/
theorem sandpile_self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    sandpUnif d N t x = sandpUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  rw [Bridge.toppleTime_eq] at ht
  rw [Bridge.sandpUnif_eq, Bridge.sandpUnif_eq]
  exact DimRed.sandpile_self_similarity N d hN hd j hj t ht x hx hxgt

end DimRed.StatementAudit.Sandpile
