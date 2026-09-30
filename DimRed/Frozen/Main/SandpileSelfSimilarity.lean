/-
Clause 2 of the Corollary to Theorem 1.1 of `dimred.tex`, frozen.
`dimred.tex:143-159`:

  "(2) Self-similarity: for all $j < M$, $t \leq \tau_j$, and
   $\mathbf{x} \in \mathcal{S}_M^{(d)}$ with $\mathbf{x} > M-j+1$,
   $s_t^{(d,N)}(\mathbf{x}) = s_t^{(d,2 j)}(\mathbf{x}-(M-j))$."

`τ_j` is `toppleTime d j`.  Vector inequalities and the subtraction of a scalar
from a vector are coordinatewise (`dimred.tex:273`).
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.sandpile_self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    sandpUnif d N t x = sandpUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ)))
-- FROZEN-STATEMENT-END
:= sandpile_self_similarity_of_reg reg_proved N d hN hd j hj t ht x hx hxgt
