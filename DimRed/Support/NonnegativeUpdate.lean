/- The nonnegative floor specialization used by the existing joint proof. -/
import DimRed.Support.Recursion

open LatticeProb DimRed

theorem DimRed.bounded_point_update (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x = (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
:= by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hb := sandp_bounds d N s₀ hs0 hs1 t x hx
  have hsucc := odo_succ_eq d N s₀ t x hx
  have hsandp : sandp d N s₀ t x
      = s₀ x + nbrSum (odo d N s₀ t) x - 2 * (d : ℤ) * odo d N s₀ t x := by
    simp only [sandp, lap]; ring
  rw [hsucc]
  refine (ediv_unique hdpos ?_ ?_).symm
  · split
    · rename_i hcase; rw [hsandp] at hcase hb; linarith [hb.1, hb.2]
    · rename_i hcase; rw [not_le, hsandp] at hcase; rw [hsandp] at hb; linarith [hb.1, hb.2]
  · split
    · rename_i hcase; rw [hsandp] at hcase hb; linarith [hb.1, hb.2]
    · rename_i hcase; rw [not_le, hsandp] at hcase; rw [hsandp] at hb; linarith [hb.1, hb.2]
