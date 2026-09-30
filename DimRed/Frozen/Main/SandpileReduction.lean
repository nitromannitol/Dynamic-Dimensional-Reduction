/-
Clause 1 of the Corollary to Theorem 1.1 of `dimred.tex`, frozen.
`dimred.tex:143-159`:

  "The results in Theorem \ref{the_theorem}, using the same notation, extend to
   the sequence of sandpiles.
   (1) Dimensional reduction: for all
   $\mathbf{x}_{d-1} \in \mathcal{S}_M^{(d-1)}$ with $\mathbf{x}_{d-1} \geq 2$,
   $s_{\infty}^{(d,N)}(\mathbf{x}_{d-1},1) =
    s_{\infty}^{(d-1,N)}(\mathbf{x}_{d-1})+2$."

The dimension is written `d + 1` in place of `d`.  `s_∞ = 2d + Δ v_∞` is
`sandpInfUnif`, an integer, `v_∞` being read through `ℕ∞`.
-/
import DimRed.Support.RegProved

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.sandpile_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    sandpInfUnif (d + 1) N (Fin.snoc x 1) = sandpInfUnif d N x + 2
-- FROZEN-STATEMENT-END
:= sandpile_dimensional_reduction_of_reg reg_proved N d hN hd x hx hx2
