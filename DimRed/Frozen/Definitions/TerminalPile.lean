/-
Terminal-pile definition of the sandpile corollary in the corrected edition. `dimred-corrected-arxiv.tex:145-161` (label
`sandpile_corollary`), where the terminal pile `s_\infty` is used; its defining
equation is the telescoped form of the recursion at
`dimred-corrected-arxiv.tex`, label `subsec:main_result` with `s_0 = 2d` and `v_0 = 0`:

  "The results in Theorem \ref{the_theorem}, using the same notation, extend
   to the sequence of sandpiles.

  s_{\infty}^{(d,N)}(\mathbf{x}_{d-1},1) =
   s_{\infty}^{(d-1,N)}(\mathbf{x}_{d-1})+2."

This unit records the terminal pile `s_∞` as its literal defining equation,
`2d` plus the Laplacian of the final odometer, which is the telescoped form of
the recursion at lines 95-96 with `s_0 ≡ 2d` and `v_0 = 0`.
-/
import DimRed.Support.SourceCarriers

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.terminal_pile_characterization (d N : ℕ) (hd : 1 ≤ d) (x : Corrected.CubeSite d N) :
    Corrected.terminalPile d N hd x =
      2 * (d : ℤ) + DimRed.lap (fun y => ((odoInfUnif d N y).toNat : ℤ)) x.val
-- FROZEN-STATEMENT-END
:= rfl
