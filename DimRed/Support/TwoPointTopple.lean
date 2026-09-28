import DimRed.Support.Recursion
import DimRed.Support.Fundamental

open LatticeProb DimRed

namespace DimRed

/-- The all-twos point of the side-`4` cube topples at the first step: its
sandpile at time zero is `2d`, which is exactly the toppling threshold. -/
theorem odoUnif_two_topple (d : ℕ) (_hd : 1 ≤ d) :
    1 ≤ odoUnif d 4 1 (fun _ : Fin d => (2 : ℤ)) := by
  have hcube : inCube d 4 (fun _ : Fin d => (2 : ℤ)) := by
    intro i
    rw [loCoord, hiCoord, sideHalf]
    norm_num
  have hstep := odo_succ_eq d 4 (fun _ => 2 * (d : ℤ)) 0 (fun _ : Fin d => (2 : ℤ)) hcube
  have hzero : odo d 4 (fun _ => 2 * (d : ℤ)) 0 (fun _ : Fin d => (2 : ℤ)) = 0 := rfl
  rw [hzero, zero_add] at hstep
  have hsand : sandp d 4 (fun _ => 2 * (d : ℤ)) 0 (fun _ : Fin d => (2 : ℤ)) = 2 * (d : ℤ) := by
    simp [sandp, lap, odo, nbrSum]
  rw [hsand] at hstep
  rw [if_pos le_rfl] at hstep
  simp only [odoUnif]
  omega

end DimRed
