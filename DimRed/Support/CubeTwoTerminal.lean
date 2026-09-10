/-
The two computations of Proposition 3.1: on the hypercube of side `2` with
`2d + (d_0 - 1)` chips at every site, the process stops after one step in
dimension `d_0` and after two steps in dimension `d_0 - 1`.
-/
import DimRed.Support.CubeTwo
import DimRed.Support.Stabilize

namespace DimRed

open LatticeProb

/-- At the critical dimension the terminal odometer is `1`. -/
theorem odoInf_cube2_critical (d₀ : ℕ) (hd₀ : 2 ≤ d₀) :
    (∀ x : Site d₀, inCube d₀ 2 x →
        odoInf d₀ 2 (fun _ => 2 * (d₀ : ℤ) + ((d₀ : ℤ) - 1)) x = 1) := by
  set c₀ : ℤ := 2 * (d₀ : ℤ) + ((d₀ : ℤ) - 1) with hc
  have hd : (2 : ℤ) ≤ (d₀ : ℤ) := by exact_mod_cast hd₀
  have h0 : ∀ y, odo d₀ 2 (fun _ => c₀) 0 y = if inCube d₀ 2 y then 0 else 0 := by
    intro y; simp [odo]
  have h1 : ∀ y, odo d₀ 2 (fun _ => c₀) 1 y = if inCube d₀ 2 y then 1 else 0 := by
    intro y
    have := odo_cube2_step d₀ c₀ 0 0 h0 y
    rw [this]
    have hcond : (2 : ℤ) * (d₀ : ℤ) ≤ c₀ := by rw [hc]; linarith
    simp [hcond]
  have h2 : ∀ y, odo d₀ 2 (fun _ => c₀) 2 y = if inCube d₀ 2 y then 1 else 0 := by
    intro y
    have := odo_cube2_step d₀ c₀ 1 1 h1 y
    rw [show (2 : ℕ) = 1 + 1 from rfl, this]
    have hno : ¬ ((2 : ℤ) * (d₀ : ℤ) ≤ c₀ - (d₀ : ℤ)) := by rw [hc]; linarith
    simp [hno]
  have hstable : odo d₀ 2 (fun _ => c₀) (1 + 1) = odo d₀ 2 (fun _ => c₀) 1 := by
    funext y; rw [show (1 : ℕ) + 1 = 2 from rfl, h2 y, h1 y]
  intro x hx
  rw [odoInf_eq_of_stable d₀ 2 (fun _ => c₀) 1 hstable x, h1 x, if_pos hx]
  rfl

/-- One dimension below the critical dimension the terminal odometer is `2`. -/
theorem odoInf_cube2_subcritical (d₀ : ℕ) (hd₀ : 2 ≤ d₀) :
    (∀ x : Site (d₀ - 1), inCube (d₀ - 1) 2 x →
      odoInf (d₀ - 1) 2 (fun _ => 2 * ((d₀ - 1 : ℕ) : ℤ) + ((d₀ : ℤ) - 1)) x = 2) := by
  set d : ℕ := d₀ - 1 with hdd
  set c₀ : ℤ := 2 * ((d : ℕ) : ℤ) + ((d₀ : ℤ) - 1) with hc
  have hD : ((d : ℕ) : ℤ) = (d₀ : ℤ) - 1 := by
    rw [hdd]; push_cast [Nat.cast_sub (by omega : 1 ≤ d₀)]; ring
  have hd₀' : (2 : ℤ) ≤ (d₀ : ℤ) := by exact_mod_cast hd₀
  have hD1 : (1 : ℤ) ≤ ((d : ℕ) : ℤ) := by rw [hD]; linarith
  have hc' : c₀ = 3 * ((d : ℕ) : ℤ) := by rw [hc, hD]; ring
  have h0 : ∀ y, odo d 2 (fun _ => c₀) 0 y = if inCube d 2 y then 0 else 0 := by
    intro y; simp [odo]
  have h1 : ∀ y, odo d 2 (fun _ => c₀) 1 y = if inCube d 2 y then 1 else 0 := by
    intro y
    have hstep := odo_cube2_step d c₀ 0 0 h0 y
    rw [hstep]
    have hcond : (2 : ℤ) * ((d : ℕ) : ℤ) ≤ c₀ := by rw [hc']; linarith
    simp [hcond]
  have h2 : ∀ y, odo d 2 (fun _ => c₀) 2 y = if inCube d 2 y then 2 else 0 := by
    intro y
    have hstep := odo_cube2_step d c₀ 1 1 h1 y
    rw [show (2 : ℕ) = 1 + 1 from rfl, hstep]
    have hcond : (2 : ℤ) * ((d : ℕ) : ℤ) ≤ c₀ - ((d : ℕ) : ℤ) := by rw [hc']; linarith
    simp [hcond]
  have h3 : ∀ y, odo d 2 (fun _ => c₀) 3 y = if inCube d 2 y then 2 else 0 := by
    intro y
    have hstep := odo_cube2_step d c₀ 2 2 h2 y
    rw [show (3 : ℕ) = 2 + 1 from rfl, hstep]
    have hno : ¬ ((2 : ℤ) * ((d : ℕ) : ℤ) ≤ c₀ - ((d : ℕ) : ℤ) * 2) := by rw [hc']; linarith
    simp [hno]
  have hstable : odo d 2 (fun _ => c₀) (2 + 1) = odo d 2 (fun _ => c₀) 2 := by
    funext y; rw [show (2 : ℕ) + 1 = 3 from rfl, h3 y, h2 y]
  intro x hx
  rw [odoInf_eq_of_stable d 2 (fun _ => c₀) 2 hstable x, h2 x, if_pos hx]
  rfl

end DimRed
