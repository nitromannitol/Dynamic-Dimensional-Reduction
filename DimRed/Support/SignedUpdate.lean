module

public import DimRed.Support.Recursion

@[expose] public section

/-!
# Signed one-step odometer update

The upper bound on the initial pile propagates under parallel toppling even when
the initial pile has negative values. This gives the exact update as the maximum
of the current odometer and the integer quotient from the point-induction
formula, without assuming a lower bound on the initial pile.
-/
open LatticeProb

namespace DimRed

/-- An upper bound on the initial pile propagates to every later sandpile, with
no lower bound on the initial pile. -/
theorem sandp_le_upper_bound (d N : ℕ) (s₀ : Site d → ℤ)
    (hs₀ : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    sandp d N s₀ t x ≤ 2 * (2 * (d : ℤ)) - 1 := by
  induction t with
  | zero =>
      rw [sandp_zero]
      exact hs₀ x hx
  | succ t ih =>
      have hnb := nbrSum_bounds
        (fun y => odo d N s₀ (t + 1) y - odo d N s₀ t y)
        (fun y => odo_succ_sub_bounds d N s₀ t y) x
      have hstep := sandp_succ d N s₀ t x
      have hfire := odo_succ_sub_eq d N s₀ t x hx
      rw [lap] at hstep
      by_cases hf : 2 * (d : ℤ) ≤ sandp d N s₀ t x
      · rw [ite_eq_left hf] at hfire
        rw [hstep, hfire]
        nlinarith [ih, hnb.2]
      · have hstable : sandp d N s₀ t x < 2 * (d : ℤ) := by omega
        rw [ite_eq_right hf] at hfire
        rw [hstep, hfire]
        nlinarith [hstable, hnb.2]

/-- Under the source upper bound, one parallel step is the current odometer
truncated below by its current value and above by the integer quotient. This
form remains valid for signed initial piles. -/
theorem odo_succ_eq_max_quotient (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs₀ : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x =
      max (odo d N s₀ t x)
        ((s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))) := by
  have hden : 0 < 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  have hupper := sandp_le_upper_bound d N s₀ hs₀ t x hx
  have hbase : s₀ x + nbrSum (odo d N s₀ t) x =
      sandp d N s₀ t x + 2 * (d : ℤ) * odo d N s₀ t x := by
    simp only [sandp, lap]
    ring
  by_cases hf : 2 * (d : ℤ) ≤ sandp d N s₀ t x
  · have hquot :
        (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
          = odo d N s₀ t x + 1 := by
      apply ediv_unique hden
      · rw [hbase]
        nlinarith
      · rw [hbase]
        nlinarith [hupper]
    calc
      odo d N s₀ (t + 1) x = odo d N s₀ t x + 1 := by
        rw [odo_succ_eq d N s₀ t x hx, ite_eq_left hf]
      _ = max (odo d N s₀ t x)
          ((s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))) := by
        rw [hquot, max_eq_right (by omega)]
  · have hstable : sandp d N s₀ t x < 2 * (d : ℤ) := by omega
    have hquot :
        (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
          ≤ odo d N s₀ t x := by
      have hlt : s₀ x + nbrSum (odo d N s₀ t) x
          < (2 * (d : ℤ)) * (odo d N s₀ t x + 1) := by
        rw [hbase]
        nlinarith
      have hquotlt := (Int.ediv_lt_iff_lt_mul hden).2 (by
        rw [mul_comm]
        exact hlt)
      omega
    calc
      odo d N s₀ (t + 1) x = odo d N s₀ t x := by
        rw [odo_succ_eq d N s₀ t x hx, ite_eq_right hf]
        simp
      _ = max (odo d N s₀ t x)
          ((s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))) := by
        rw [max_eq_left hquot]

-- These examples check the signed edge case and a nonnegative firing step.
example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) = 0 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) ≠
      ((-1 : ℤ) + nbrSum (odo 1 4 (fun _ => (-1 : ℤ)) 0) (fun _ => (1 : ℤ))) / 2 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) =
      max (odo 1 4 (fun _ => (-1 : ℤ)) 0 (fun _ => (1 : ℤ)))
        (((-1 : ℤ) + nbrSum (odo 1 4 (fun _ => (-1 : ℤ)) 0)
          (fun _ => (1 : ℤ))) / 2) := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

example :
    odo 1 4 (fun _ => (2 : ℤ)) 1 (fun _ => (1 : ℤ)) =
      max (odo 1 4 (fun _ => (2 : ℤ)) 0 (fun _ => (1 : ℤ)))
        ((2 + nbrSum (odo 1 4 (fun _ => (2 : ℤ)) 0) (fun _ => (1 : ℤ))) / 2) := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

end DimRed
