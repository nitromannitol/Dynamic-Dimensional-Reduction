/-
The second display of Theorem 1.1(i) of `dimred.tex`, frozen.
`dimred.tex:109-140` (label `the_theorem`), clause 1:

  "and for $\mathbf{x}_{d-1} \geq 2$,
   $v_{\infty}^{(d,N)}(\mathbf{x}_{d-1}, 2) = v_{\infty}^{(d-1,N)}
   (\mathbf{x}_{d-1})$."

The dimension is written `d + 1` in place of `d`.  `v_∞` is `odoInf`, valued in
`ℕ∞`; that it is finite is a theorem of the development.  Vector inequalities
are coordinatewise (`dimred.tex:263-266`).
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.terminal_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) N (Fin.snoc x 2) = odoInfUnif d N x
-- FROZEN-STATEMENT-END
:= by sorry
