/-
Proposition 3.1 of `dimred.tex`, frozen.  `dimred.tex:706-708`:

  "When $s_0^{(d)} \equiv 2 d + (d_0-1)$, $v_\infty^{(d_0)} \equiv 1$ but
   $v_\infty^{(d_0-1)} \equiv 2$."

The setting is `M = 1`, that is, the hypercube of side `N = 2`
(`dimred.tex:700-705`), and `d_0 ≥ 2` because a zero-dimensional sandpile is not
defined (`dimred.tex:705`).  In dimension `d` the initial sandpile is
`2d + (d_0 - 1)` chips at every site, so it is `2 d_0 + (d_0-1)` in dimension
`d_0` and `2(d_0-1) + (d_0-1)` in dimension `d_0 - 1`.
-/
import DimRed.Support.CubeTwoTerminal

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.no_reduction_at_critical_dimension (d₀ : ℕ) (hd₀ : 2 ≤ d₀) :
    (∀ x : Site d₀, inCube d₀ 2 x →
        odoInf d₀ 2 (fun _ => 2 * (d₀ : ℤ) + ((d₀ : ℤ) - 1)) x = 1) ∧
      (∀ x : Site (d₀ - 1), inCube (d₀ - 1) 2 x →
        odoInf (d₀ - 1) 2 (fun _ => 2 * ((d₀ - 1 : ℕ) : ℤ) + ((d₀ : ℤ) - 1)) x = 2)
-- FROZEN-STATEMENT-END
:= ⟨DimRed.odoInf_cube2_critical d₀ hd₀, DimRed.odoInf_cube2_subcritical d₀ hd₀⟩
