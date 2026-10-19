import DimRed.Support.AxisStep

/-!
The strong facet compatibility clause in dimension one, `dimred-corrected-arxiv.tex:839-844`.
At the first facet site reflection identifies the left neighbour with the site
itself, while the derivative bound forces the adjacent site to topple.
-/
namespace DimRed

open LatticeProb

theorem odo_one_strong_facet (M t : ℕ) (hM : 2 ≤ M) (y : Site 1) (hy : y 0 = 1)
    (hderiv : odoUnif 1 (2 * M) t y - odoUnif 1 (2 * M) t (y + unit 0 + unit 0) ≤ 2 * y 0)
    (h : odoUnif 1 (2 * M) t y = odoUnif 1 (2 * M) t (y + unit 0) + 1) :
      odoUnif 1 (2 * M) (t + 1) y = odoUnif 1 (2 * M) t y
        ∧ odoUnif 1 (2 * M) (t + 1) (y + unit 0) = odoUnif 1 (2 * M) t (y + unit 0) + 1 := by
  simp only [odoUnif, Nat.cast_one, mul_one] at hderiv h ⊢
  have hycube : inCube 1 (2 * M) y := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [hy, loCoord_two_mul, hiCoord_two_mul]
    omega
  have hypluscube : inCube 1 (2 * M) (y + unit 0) := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [add_unit_self, hy, loCoord_two_mul, hiCoord_two_mul]
    omega
  have hreflect := odo_reflect_coord 1 M 2 t y 0
  have he : (fun k : Fin 1 => if k = (0 : Fin 1) then 1 - y 0 else y k) = y - unit 0 := by
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst hk
    simp [unit, hy]
  rw [he] at hreflect
  have hlap_y : lap (odo 1 (2 * M) (fun _ => 2) t) y =
      odo 1 (2 * M) (fun _ => 2) t (y + unit 0) - odo 1 (2 * M) (fun _ => 2) t y := by
    rw [lap, nbrSum, Fin.sum_univ_one, hreflect]
    ring
  have hs_y : sandp 1 (2 * M) (fun _ => 2) t y = 1 := by
    rw [sandp, hlap_y]
    linarith
  have hnot_y : ¬ (2 : ℤ) * ((1 : ℕ) : ℤ) ≤ sandp 1 (2 * M) (fun _ => 2) t y := by
    rw [hs_y]
    omega
  have hlap_yplus : 0 ≤ lap (odo 1 (2 * M) (fun _ => 2) t) (y + unit 0) := by
    rw [lap, nbrSum, Fin.sum_univ_one]
    have heq : y + unit 0 - unit 0 = y := by abel
    rw [heq]
    rw [hy] at hderiv
    norm_num at hderiv ⊢
    linarith [hderiv, h]
  have hfire_yplus : (2 : ℤ) * ((1 : ℕ) : ℤ) ≤ sandp 1 (2 * M) (fun _ => 2) t (y + unit 0) := by
    simp only [sandp]
    norm_num
    linarith [hlap_yplus]
  constructor
  · rw [odo_succ_eq 1 (2 * M) (fun _ => 2) t y hycube]
    simp only [if_neg hnot_y, add_zero]
  · rw [odo_succ_eq 1 (2 * M) (fun _ => 2) t (y + unit 0) hypluscube,
      if_pos hfire_yplus]

end DimRed
