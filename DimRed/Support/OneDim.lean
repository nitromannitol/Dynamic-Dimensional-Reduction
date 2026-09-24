/-
The one-dimensional odometer recursion and its first two time slices for the
uniform sandpile on `C_{2M}^{(1)}`, together with the `M = 2` table of
`dimred.tex:955-970`.
-/
import DimRed.Support.DerivBound

namespace DimRed

open LatticeProb

/-- The one-dimensional point-induction recursion, `dimred.tex:955-958`. -/
theorem odo_one_succ (M t : ℕ) (y : Site 1) (hy0 : 2 ≤ y 0) (hyM : y 0 ≤ (M : ℤ)) :
    odoUnif 1 (2 * M) (t + 1) y =
      1 + (odoUnif 1 (2 * M) t (y + unit 0) +
        odoUnif 1 (2 * M) t (y - unit 0)) / 2 := by
  have hy : inCube 1 (2 * M) y := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul]
    omega
  change odo 1 (2 * M) (fun _ => 2) (t + 1) y =
    1 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
      odo 1 (2 * M) (fun _ => 2) t (y - unit 0)) / 2
  rw [Frozen.pt_ind_lemma 1 (2 * M) (by norm_num) (fun _ => 2) (by
    intro z _
    norm_num) (by
    intro z _
    norm_num) t y hy]
  simp only [nbrSum, Fin.sum_univ_one]
  norm_num
  rw [show 2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
      odo 1 (2 * M) (fun _ => 2) t (y - unit 0)) =
      (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
        odo 1 (2 * M) (fun _ => 2) t (y - unit 0)) + 2 * 1 by ring,
    Int.add_mul_ediv_left _ 1 (by norm_num)]
  ring

/-- Reflection across the origin in the one-dimensional folded domain. -/
theorem odo_one_reflect (M t : ℕ) (y : Site 1) (hy : y 0 = 1) :
    odoUnif 1 (2 * M) t (y - unit 0) = odoUnif 1 (2 * M) t y := by
  simpa [odoUnif] using odo_sub_unit_of_one 1 M 2 t y 0 hy

/-- The recursion at the reflecting site `1`, `dimred.tex:955-958`. -/
theorem odo_one_succ_at_one (M t : ℕ) (y : Site 1) (hM : 1 ≤ M) (hy : y 0 = 1) :
    odoUnif 1 (2 * M) (t + 1) y =
      1 + (odoUnif 1 (2 * M) t (y + unit 0) + odoUnif 1 (2 * M) t y) / 2 := by
  have hycube : inCube 1 (2 * M) y := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul, hy]
    omega
  change odo 1 (2 * M) (fun _ => 2) (t + 1) y =
    1 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
      odo 1 (2 * M) (fun _ => 2) t y) / 2
  rw [Frozen.pt_ind_lemma 1 (2 * M) (by norm_num) (fun _ => 2) (by
    intro z _
    norm_num) (by
    intro z _
    norm_num) t y hycube]
  simp only [nbrSum, Fin.sum_univ_one]
  norm_num
  have href : odo 1 (2 * M) (fun _ => 2) t (y - unit 0) =
      odo 1 (2 * M) (fun _ => 2) t y := by
    simpa [odoUnif] using odo_one_reflect M t y hy
  rw [href]
  rw [show 2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
      odo 1 (2 * M) (fun _ => 2) t y) =
      (odo 1 (2 * M) (fun _ => 2) t (y + unit 0) +
        odo 1 (2 * M) (fun _ => 2) t y) + 2 * 1 by ring,
    Int.add_mul_ediv_left _ 1 (by norm_num)]
  ring

/-- The first parallel toppling, `dimred.tex:959`. -/
theorem odo_one_time_one (M : ℕ) (_hM : 1 ≤ M) (y : Site 1) (hy : inCube 1 (2 * M) y) :
    odoUnif 1 (2 * M) 1 y = 1 := by
  simp only [odoUnif, odo, lap, nbrSum]
  rw [if_pos hy]
  norm_num

/-- The second parallel toppling in the folded half of the interval,
`dimred.tex:960-961`. -/
theorem odo_one_time_two (M : ℕ) (hM : 2 ≤ M) :
    (∀ y : Site 1, inCube 1 (2 * M) y → 1 ≤ y 0 → y 0 < (M : ℤ) →
      odoUnif 1 (2 * M) 2 y = 2) ∧
    ∀ y : Site 1, inCube 1 (2 * M) y → y 0 = (M : ℤ) →
      odoUnif 1 (2 * M) 2 y = 1 := by
  constructor
  · intro y hycube hy1 hyM
    by_cases hyone : y 0 = 1
    · rw [show (2 : ℕ) = 1 + 1 by omega, odo_one_succ_at_one M 1 y (by omega) hyone]
      have hplus : inCube 1 (2 * M) (y + unit 0) := by
        intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst i
        rw [add_unit_self, loCoord_two_mul, hiCoord_two_mul]
        omega
      have hself : odoUnif 1 (2 * M) 1 y = 1 := odo_one_time_one M (by omega) y hycube
      have hplus' : odoUnif 1 (2 * M) 1 (y + unit 0) = 1 :=
        odo_one_time_one M (by omega) (y + unit 0) hplus
      rw [hplus', hself]
      norm_num
    · have hy2 : 2 ≤ y 0 := by omega
      rw [show (2 : ℕ) = 1 + 1 by omega, odo_one_succ M 1 y hy2 (le_of_lt hyM)]
      have hplus : inCube 1 (2 * M) (y + unit 0) := by
        intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst i
        rw [add_unit_self, loCoord_two_mul, hiCoord_two_mul]
        omega
      have hminus : inCube 1 (2 * M) (y - unit 0) := by
        intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst i
        rw [sub_unit_self, loCoord_two_mul, hiCoord_two_mul]
        omega
      rw [odo_one_time_one M (by omega) (y + unit 0) hplus,
        odo_one_time_one M (by omega) (y - unit 0) hminus]
      norm_num
  · intro y hycube hyM
    have hyM2 : 2 ≤ y 0 := by rw [hyM]; exact_mod_cast hM
    rw [show (2 : ℕ) = 1 + 1 by omega, odo_one_succ M 1 y hyM2 (le_of_eq hyM)]
    have hplus : ¬ inCube 1 (2 * M) (y + unit 0) := by
      intro hplus
      have hi := hplus (0 : Fin 1)
      rw [add_unit_self, loCoord_two_mul, hiCoord_two_mul, hyM] at hi
      omega
    have hminus : inCube 1 (2 * M) (y - unit 0) := by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      rw [sub_unit_self, loCoord_two_mul, hiCoord_two_mul, hyM]
      omega
    rw [show odoUnif 1 (2 * M) 1 (y + unit 0) = 0 by
      simp only [odoUnif, odo, if_neg hplus],
      odo_one_time_one M (by omega) (y - unit 0) hminus]
    norm_num

/-- The explicit `M = 2` time table, `dimred.tex:957-965`. -/
theorem odo_one_M_two :
    (odoUnif 1 4 1 (fun _ => (1 : ℤ)) = 1) ∧
    (odoUnif 1 4 1 (fun _ => (2 : ℤ)) = 1) ∧
    (odoUnif 1 4 2 (fun _ => (1 : ℤ)) = 2) ∧
    (odoUnif 1 4 2 (fun _ => (2 : ℤ)) = 1) ∧
    (odoUnif 1 4 3 (fun _ => (1 : ℤ)) = 2) ∧
    (odoUnif 1 4 3 (fun _ => (2 : ℤ)) = 2) ∧
    (odoUnif 1 4 4 (fun _ => (1 : ℤ)) = 3) ∧
    (odoUnif 1 4 4 (fun _ => (2 : ℤ)) = 2) := by
  decide

end DimRed
