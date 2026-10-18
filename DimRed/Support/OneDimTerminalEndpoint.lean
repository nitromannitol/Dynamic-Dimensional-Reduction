import DimRed.Support.OneDimTerminal
import DimRed.Support.Recursion

/-
The full printed legal interval of the one-dimensional terminal derivative,
including the endpoint `x₀ = M`.  The strict branch is `odoInf_one_deriv`; at
the endpoint the shifted site lies outside the cube, so its terminal odometer
vanishes, while `odoInf_one_eq` gives the value `M` at `x₀ = M`.
-/

open DimRed LatticeProb

theorem DimRed.Corrected.one_terminal_derivative (M : ℕ) (hM : 1 ≤ M)
    (x : Site 1) (hx1 : 1 ≤ x 0) (hxM : x 0 ≤ (M : ℤ)) :
    ((odoInfUnif 1 (2 * M) x).toNat : ℤ) -
      ((odoInfUnif 1 (2 * M) (x + unit (0 : Fin 1))).toNat : ℤ) = x 0 := by
  by_cases hlt : x 0 < (M : ℤ)
  · exact odoInf_one_deriv M hM x hx1 hlt
  · have heq : x 0 = (M : ℤ) := by omega
    have hA : (odoInfUnif 1 (2 * M) x).toNat = M := by
      rw [odoInf_one_eq M hM x hx1 hxM, ENat.toNat_coe]
      have hpoly : (M : ℤ) * ((M : ℤ) + 1) - x 0 * (x 0 - 1) = 2 * (M : ℤ) := by
        rw [heq]
        ring
      have h2 : ((M : ℤ) * ((M : ℤ) + 1) - x 0 * (x 0 - 1)) / 2 = (M : ℤ) := by
        rw [hpoly]
        omega
      rw [h2]
      simp
    have hout : ¬ inCube 1 (2 * M) (x + (unit (0 : Fin 1) : Site 1)) := by
      intro h
      have h0 := h (0 : Fin 1)
      rw [loCoord_two_mul, hiCoord_two_mul, one_coord_add] at h0
      omega
    have hB : odoInfUnif 1 (2 * M) (x + (unit (0 : Fin 1) : Site 1)) = 0 := by
      have hz : ∀ (s : Site 1 → ℤ) (t : ℕ),
          odo 1 (2 * M) s t (x + (unit (0 : Fin 1) : Site 1)) = 0 :=
        fun s t => odo_eq_zero_outside 1 (2 * M) s t _ hout
      simp [odoInfUnif, odoInf, hz]
    rw [hA, hB]
    simp [heq]

example : ((odoInfUnif 1 (2 * 1) (fun _ => 1 : Site 1)).toNat : ℤ) -
    ((odoInfUnif 1 (2 * 1) ((fun _ => 1 : Site 1) + unit (0 : Fin 1))).toNat : ℤ) = 1 :=
  DimRed.Corrected.one_terminal_derivative 1 (by norm_num) (fun _ => 1) (by norm_num)
    (by norm_num)

example : ((odoInfUnif 1 (2 * 2) (fun _ => 1 : Site 1)).toNat : ℤ) -
    ((odoInfUnif 1 (2 * 2) ((fun _ => 1 : Site 1) + unit (0 : Fin 1))).toNat : ℤ) = 1 :=
  DimRed.Corrected.one_terminal_derivative 2 (by norm_num) (fun _ => 1) (by norm_num)
    (by norm_num)
