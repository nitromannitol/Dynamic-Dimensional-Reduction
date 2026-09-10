/-
Lemma 3.1 of `dimred.tex`, frozen.  `dimred.tex:728-733`:

  "If we define $0 = v_t(d+1) = v_t(-1)$, then
   $\Delta v_t(x) = (-d - x) v_t(x) + (d-x) v_t(x+1) + x v_t(x-1)$."

This is the radial reparameterization of `S_2^{(d)}` of `dimred.tex:724-727`:
every `x ∈ S_2^{(d)}` is `(2_x, 1_{d-x})` for some `0 ≤ x ≤ d`, which is
`radial d x`, and the hypercube is `C_4^{(d)}` since `N = 2M` and `M = 2`
(`dimred.tex:428-431`).  The paper's convention `v_t(d+1) = v_t(-1) = 0` is not
needed here: the coefficient of the first is `d - x`, which vanishes at `x = d`,
and the coefficient of the second is `x`, which vanishes at `x = 0`.  The
initial sandpile is constant, hence symmetric, which is all the proof uses.
-/
import DimRed.Support.Radial

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.radial_laplacian (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    lap (odo d 4 (fun _ => c) t) (radial d k)
      = (-(d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d k)
        + ((d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d (k + 1))
        + (k : ℤ) * odo d 4 (fun _ => c) t (radial d (k - 1))
-- FROZEN-STATEMENT-END
:= DimRed.lap_radial d c t k hk
