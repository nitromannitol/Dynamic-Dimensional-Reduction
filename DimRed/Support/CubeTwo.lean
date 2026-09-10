/-
The hypercube of side `2`, the setting `M = 1` of `dimred.tex:704-720`: every
site is a corner with `d` neighbours inside the cube, so a constant odometer has
Laplacian `-d` times its value, and the whole process is one scalar recursion.
-/
import DimRed.Support.Symmetry

namespace DimRed

open LatticeProb

theorem loCoord_two : loCoord 2 = 0 := by norm_num [loCoord]

theorem hiCoord_two : hiCoord 2 = 1 := by norm_num [hiCoord, sideHalf]

theorem inCube_two_iff (d : ℕ) (x : Site d) :
    inCube d 2 x ↔ ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [inCube, loCoord_two, hiCoord_two]

theorem unit_apply_self (d : ℕ) (i : Fin d) : (unit i : Site d) i = 1 := by
  simp [unit]

theorem unit_apply_ne (d : ℕ) (i j : Fin d) (h : j ≠ i) : (unit i : Site d) j = 0 := by
  simp [unit, h]

theorem inCube_two_add (d : ℕ) (x : Site d) (hx : inCube d 2 x) (i : Fin d) :
    inCube d 2 (x + unit i) ↔ x i = 0 := by
  rw [inCube_two_iff] at hx ⊢
  constructor
  · intro h
    have h1 := (h i).2
    have h2 := (hx i).1
    rw [Pi.add_apply, unit_apply_self] at h1
    omega
  · intro h0 j
    by_cases hj : j = i
    · subst hj; rw [Pi.add_apply, unit_apply_self, h0]; omega
    · rw [Pi.add_apply, unit_apply_ne d i j hj, add_zero]; exact hx j

theorem inCube_two_sub (d : ℕ) (x : Site d) (hx : inCube d 2 x) (i : Fin d) :
    inCube d 2 (x - unit i) ↔ x i = 1 := by
  rw [inCube_two_iff] at hx ⊢
  constructor
  · intro h
    have h1 := (h i).1
    have h2 := (hx i).2
    rw [Pi.sub_apply, unit_apply_self] at h1
    omega
  · intro h1 j
    by_cases hj : j = i
    · subst hj; rw [Pi.sub_apply, unit_apply_self, h1]; omega
    · rw [Pi.sub_apply, unit_apply_ne d i j hj, sub_zero]; exact hx j

theorem nbrSum_cube2 (d : ℕ) (a : ℤ) (x : Site d) (hx : inCube d 2 x) :
    nbrSum (fun y => if inCube d 2 y then a else 0) x = a * (d : ℤ) := by
  have key : ∀ i : Fin d,
      ((if inCube d 2 (x + unit i) then a else 0)
        + (if inCube d 2 (x - unit i) then a else 0)) = a := by
    intro i
    have hxi := (inCube_two_iff d x).1 hx i
    by_cases h0 : x i = 0
    · rw [if_pos ((inCube_two_add d x hx i).2 h0), if_neg]
      · ring
      · rw [inCube_two_sub d x hx i]; omega
    · have h1 : x i = 1 := by omega
      rw [if_neg, if_pos ((inCube_two_sub d x hx i).2 h1)]
      · ring
      · rw [inCube_two_add d x hx i]; omega
  simp only [nbrSum, key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_comm]

/-- On the hypercube of side `2` a constant initial sandpile keeps the odometer
constant on the cube, and the constant advances by one exactly when the site is
unstable. -/
theorem odo_cube2_step (d : ℕ) (c₀ : ℤ) (t : ℕ) (a : ℤ)
    (h : ∀ y, odo d 2 (fun _ => c₀) t y = if inCube d 2 y then a else 0) (x : Site d) :
    odo d 2 (fun _ => c₀) (t + 1) x
      = if inCube d 2 x then (a + (if 2 * (d : ℤ) ≤ c₀ - (d : ℤ) * a then 1 else 0)) else 0 := by
  have hfun : odo d 2 (fun _ => c₀) t = fun y => if inCube d 2 y then a else 0 := funext h
  by_cases hx : inCube d 2 x
  · have harith : c₀ + (-(2 * (d : ℤ)) * a + a * (d : ℤ)) = c₀ - (d : ℤ) * a := by ring
    simp only [odo, if_pos hx, lap, hfun, nbrSum_cube2 d a x hx, harith]
  · simp only [odo, if_neg hx]

end DimRed
