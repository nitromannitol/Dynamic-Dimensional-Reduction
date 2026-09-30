/-
The first step of the base case of `dimred.tex:789-813`: at `t = 1` every
radial site of `S_2^{(d)}` topples, because the initial sandpile
`s_0 = 2d + (d-1)` is at least `2d` and the odometer starts at zero.
-/
import DimRed.Support.Radial

namespace DimRed

open LatticeProb

/-- `v_1(x) = v_0(x) + 1` at every radial site, `dimred.tex:816`. -/
theorem odo_radial_one (d : ℕ) (hd : 1 ≤ d) (x : ℕ) (_hx : x ≤ d) :
    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) 1 (radial d x)
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) 0 (radial d x) + 1 := by
  rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) 0 (radial d x)
    (inCube_radial d x)]
  simp only [odo, sandp, lap, nbrSum, Finset.sum_const_zero, mul_zero, add_zero]
  rw [if_pos (by omega)]

end DimRed
