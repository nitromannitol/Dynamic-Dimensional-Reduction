module

public import DimRed.Support.SignedUpdate
public import DimRed.Support.Stabilize

@[expose] public section

/-!
# Signed one-step odometer update with zero truncation

For signed initial piles satisfying the source upper bound, the quotient in
the point-induction formula is nondecreasing in time. This removes the
dependence on the current odometer from the one-step maximum formula.
-/
open LatticeProb

namespace DimRed

/-- Under the source upper bound, the next odometer is the maximum of zero and
the integer quotient from the point-induction formula. -/
theorem odo_succ_eq_max_zero_quotient (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs₀ : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x =
      max 0 ((s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))) := by
  let q : ℕ → ℤ := fun n =>
    (s₀ x + nbrSum (odo d N s₀ n) x) / (2 * (d : ℤ))
  have hden : 0 < 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  have hq_mono : ∀ n, q n ≤ q (n + 1) := by
    intro n
    have hodo : ∀ y, odo d N s₀ n y ≤ odo d N s₀ (n + 1) y :=
      fun y => odo_mono d N s₀ (Nat.le_succ n) y
    have hnb := nbrSum_mono hodo x
    apply (Int.le_ediv_iff_mul_le hden).2
    calc
      q n * (2 * (d : ℤ)) ≤ s₀ x + nbrSum (odo d N s₀ n) x := by
        dsimp [q]
        exact Int.ediv_mul_le _ (Int.ne_of_gt hden)
      _ ≤ s₀ x + nbrSum (odo d N s₀ (n + 1)) x := by
        linarith
  induction t with
  | zero =>
      simpa only [q, odo] using
        (odo_succ_eq_max_quotient d N hd s₀ hs₀ 0 x hx)
  | succ t ih =>
      rw [odo_succ_eq_max_quotient d N hd s₀ hs₀ (t + 1) x hx, ih,
        max_assoc, max_eq_right (hq_mono t)]

-- A signed initial pile below zero gives zero odometer at this site.
example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) = 0 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) =
      max 0 (((-1 : ℤ) + nbrSum (odo 1 4 (fun _ => (-1 : ℤ)) 0)
        (fun _ => (1 : ℤ))) / 2) := by
  have hx : inCube 1 4 (fun _ => (1 : ℤ)) := by
    intro i
    fin_cases i
    norm_num [inCube, loCoord, hiCoord, sideHalf]
  have hs₀ : ∀ y : Site 1, inCube 1 4 y →
      (fun _ => (-1 : ℤ)) y ≤ 2 * (2 * (1 : ℤ)) - 1 := by
    intro y hy
    norm_num
  simpa using odo_succ_eq_max_zero_quotient 1 4 (by omega) (fun _ => -1)
    hs₀ 0 (fun _ => 1) hx

-- The old untruncated quotient equation fails for this signed example.
example :
    odo 1 4 (fun _ => (-1 : ℤ)) 1 (fun _ => (1 : ℤ)) ≠
      ((-1 : ℤ) + nbrSum (odo 1 4 (fun _ => (-1 : ℤ)) 0)
        (fun _ => (1 : ℤ))) / 2 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

end DimRed
