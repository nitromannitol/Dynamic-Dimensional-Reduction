import DimRed.Support.DerivBound

/-
Weak compatibility at the all-ones facet: a height difference of one forces
the facet site not to topple at the next parallel step, as in the weak facet
compatibility clauses (`base_dimension:weak_compatability`) of `dimred-corrected-arxiv.tex`.
-/
namespace DimRed

open LatticeProb

theorem lap_odoUnif_ones (d M t : ℕ) (y : Site d) (hy : ∀ a, y a = 1)
    (a0 : Fin d)
    (h : odoUnif d (2 * M) t y = odoUnif d (2 * M) t (y + unit a0) + 1) :
    lap (odo d (2 * M) (fun _ => 2 * (d : ℤ)) t) y = -(d : ℤ) := by
  let v : Site d → ℤ := odo d (2 * M) (fun _ => 2 * (d : ℤ)) t
  have h' : v y = v (y + unit a0) + 1 := by
    simpa [v, odoUnif] using h
  have hminus : ∀ l : Fin d, v (y - unit l) = v y := by
    intro l
    have hl := odo_sub_unit_of_one d M (2 * (d : ℤ)) t y l (hy l)
    simpa [v] using hl
  have hplus : ∀ l : Fin d, v (y + unit l) = v (y + unit a0) := by
    intro l
    by_cases hla : l = a0
    · subst l
      rfl
    · have hl := odo_swap_add d M (2 * (d : ℤ)) t y l a0 hla (by
        rw [hy l, hy a0])
      simpa [v] using hl
  have hplus' : ∀ l : Fin d, v (y + unit l) = v y - 1 := by
    intro l
    rw [hplus l]
    linarith
  have hsum : nbrSum v y = 2 * (d : ℤ) * v y - (d : ℤ) := by
    calc
      nbrSum v y = ∑ i : Fin d, (v (y + unit i) + v (y - unit i)) := rfl
      _ = ∑ i : Fin d, ((v y - 1) + v y) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hplus' i, hminus i]
      _ = 2 * (d : ℤ) * v y - (d : ℤ) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring
  calc
    lap v y = -(2 * (d : ℤ)) * v y + nbrSum v y := rfl
    _ = -(d : ℤ) := by rw [hsum]; ring

theorem odo_weak_facet_ones (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (y : Site d)
    (hy : ∀ a, y a = 1) (a0 : Fin d)
    (h : odoUnif d (2 * M) t y = odoUnif d (2 * M) t (y + unit a0) + 1) :
      odoUnif d (2 * M) (t + 1) y = odoUnif d (2 * M) t y := by
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast (show 1 ≤ M by omega)
  have hycube : inCube d (2 * M) y := by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul, hy i]
    omega
  have hlap := lap_odoUnif_ones d M t y hy a0 h
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) y =
    odo d (2 * M) (fun _ => 2 * (d : ℤ)) t y
  rw [odo_succ_eq d (2 * M) (fun _ => 2 * (d : ℤ)) t y hycube]
  simp only [sandp, hlap]
  split <;> omega

theorem odo_one_weak_facet (M t : ℕ) (hM : 2 ≤ M) (_ht : 1 ≤ t) (y : Site 1) (hy : y 0 = 1)
    (h : odoUnif 1 (2 * M) t y = odoUnif 1 (2 * M) t (y + unit 0) + 1) :
      odoUnif 1 (2 * M) (t + 1) y = odoUnif 1 (2 * M) t y := by
  have hy' : ∀ a : Fin 1, y a = 1 := by
    intro a
    have ha : a = 0 := Fin.eq_zero a
    simpa [ha] using hy
  exact odo_weak_facet_ones 1 M t (by omega) hM y hy' 0 h

end DimRed
