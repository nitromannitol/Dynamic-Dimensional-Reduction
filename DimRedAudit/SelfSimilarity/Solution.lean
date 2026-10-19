import Mathlib
import DimRed.MainTheorems
import DimRedAudit.SelfSimilarity.SolutionBasic
import DimRedAudit.Support.SelfSimilarityBridge

/-!
# Solution: SelfSimilarity (Theorem 1.1(ii))

The challenge module `DimRedAudit/SelfSimilarity/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the repository
together with `DimRedAudit.SelfSimilarity.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `DimRed.self_similarity`
(`DimRed/MainTheorems.lean`) through the bridges in
`DimRedAudit/Support/SelfSimilarityBridge.lean`.
-/

namespace DimRed.StatementAudit.SelfSimilarity

/-- **Theorem 1.1(ii)** (`the_theorem`, `dimred-corrected-arxiv.tex:122-133`): self-similarity, for all
`j < M`, `t ≤ τ_j` and `x ∈ S_M^{(d)}` with `x > M - j`,
`v_t^{(d,N)}(x) = v_t^{(d,2j)}(x - (M - j))`. -/
theorem self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    odoUnif d N t x = odoUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  rw [Bridge.toppleTime_eq] at ht
  rw [Bridge.odoUnif_eq, Bridge.odoUnif_eq]
  exact DimRed.self_similarity N d hN hd j hj t ht x hx hxgt

end DimRed.StatementAudit.SelfSimilarity
