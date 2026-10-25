module

/-
Corollary to Theorem 1.1 of the corrected edition.
`dimred-corrected-arxiv.tex:155-158` (label `sandpile_corollary`), clause 2:

  "\item{Self-similarity:} for all $j < M$, $t \leq \tau_j$, and $\mathbf{x}
   \in \mathcal{S}_M^{(d)}$ with $\mathbf{x} > M-j+1$ s_t^{(d,N)}(\mathbf{x})
   = s_t^{(d,2 j)}(\mathbf{x}-(M-j))."

`τ_j` is `toppleTime d j`. Vector inequalities and the subtraction of a scalar
from a vector are coordinatewise (`dimred-corrected-arxiv.tex`, label `subsec:notation`).
-/
public import DimRed.Support.RegProved
public import DimRed.Support.SourceCarriers

@[expose] public section

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.sandpile_self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    Corrected.pile d N (fun _ => 2 * (d : ℤ)) t (Corrected.cubeSimplexSite d N hN x hx) =
      Corrected.pile d (2 * j) (fun _ => 2 * (d : ℤ)) t
        (Corrected.cubeShiftedSite N d j hN (by omega) hj x hx hxgt)
-- FROZEN-STATEMENT-END
:= sandpile_self_similarity_of_reg reg_proved N d hN hd j hj t ht x hx hxgt
