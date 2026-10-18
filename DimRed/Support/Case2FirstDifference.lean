import DimRed.Support.Case2FirstWait
import DimRed.Support.Case2QuadraticBarrier
import DimRed.Support.DerivBound

/-!
# First differences for the uniform even-cube odometer

For the actual simultaneous process started from the constant pile `2d`, the
quadratic barrier bounds the odometer by `M` on every dissipating face. The
parabolic derivative comparison then gives the upper first-difference bound,
and reflection-axis monotonicity gives its lower bound. The odometer is the
physical zero extension defined by `odo` outside the even cube.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- On the positive orthant of the physical even cube, the actual uniform
odometer has a nonnegative first difference bounded by the selected coordinate.
The face bound comes from `case2_odo_le_M_at_face` and the exact update is the
paper's floor recursion. -/
theorem case2_odo_first_difference (d M t : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (k : Fin d) (x : Site d)
    (hx : ∀ i : Fin d, 1 ≤ x i ∧ x i ≤ (M : ℤ)) :
    0 ≤ odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k) ∧
      odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k) ≤ x k := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hc0 : 0 ≤ 2 * (d : ℤ) := by positivity
  have hc1 : 2 * (d : ℤ) ≤ 2 * (2 * (d : ℤ)) - 1 := by nlinarith
  have haxis := odo_axis_refl d M hd (2 * (d : ℤ)) hc0 hc1 t x k (hx k).1
  have hcornerCube : inCube d (2 * M) (cornerPoint d M) := by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul]
    simp only [cornerPoint]
    split_ifs <;> omega
  let j : Fin d := ⟨0, by omega⟩
  have hcornerFace : cornerPoint d M j = (M : ℤ) := by
    simp [cornerPoint, j]
  have hcorner : ∀ s,
      odo d (2 * M) (fun _ => 2 * (d : ℤ)) s (cornerPoint d M) ≤
        (1 : ℤ) * (M : ℤ) := by
    intro s
    have hcap := case2_odo_le_M_at_face d M s hd hM j (cornerPoint d M)
      hcornerCube hcornerFace
    simpa [odoUnif] using hcap
  have hupper := odo_deriv_bound d M hd (2 * (d : ℤ)) hc0 hc1 1
    (by norm_num) hcorner t k x (hx k).1
  constructor
  · simpa [odoUnif] using sub_nonneg.mpr haxis
  · simpa [odoUnif] using hupper

example :
    ∃ x : Site 1, ∃ k : Fin 1,
      (∀ i : Fin 1, 1 ≤ x i ∧ x i ≤ (1 : ℤ)) ∧
        odoUnif 1 2 1 x - odoUnif 1 2 1 (x + unit k) = x k := by
  refine ⟨oneSite 1, ⟨0, ?_⟩⟩
  constructor
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num [oneSite]
  ·
    have hx : inCube 1 2 (oneSite 1) := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num [loCoord, hiCoord, sideHalf, oneSite]
    have hout : ¬ inCube 1 2 (oneSite 1 + unit (0 : Fin 1)) := by
      intro hc
      have h := (hc 0).2
      rw [add_unit_self] at h
      norm_num [hiCoord, sideHalf, oneSite] at h
    rw [odoUnif_one 1 2 (by norm_num) (oneSite 1) hx,
      odoUnif_one_outside 1 2 _ hout]
    norm_num [oneSite]

end DimRed
