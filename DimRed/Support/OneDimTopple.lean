import DimRed.Support.AxisStep
import DimRed.Frozen.Prelim.ToppleLimit

/-!
The one-dimensional strong topple comparison at the first admissible time,
`dimred.tex:1037-1105`.  The proof isolates the self-similarity, lower-
dimensional strong topple, weak facet, and topple-time inputs used by the
three cases in the paper.
-/
namespace DimRed

open LatticeProb

/- The first case is the self-similar case `y ≥ 3`; the two central cases are
   deliberately supplied together because their missing regularity input is
   not proved in this file. -/
theorem odo_one_strong_topple_at (M : ℕ) (hM : 2 ≤ M) (T : ℕ)
    (hT : toppleTime 1 (M - 1) = (T : ℕ∞))
    (hconsist : ∀ (y : ℤ), 3 ≤ y → y ≤ (M : ℤ) →
      odoUnif 1 (2 * M) (T + 1) (fun _ => y) -
          odoUnif 1 (2 * M) (T - 1) (fun _ => y) =
        odoUnif 1 (2 * (M - 1)) (T + 1) (fun _ => y - 1) -
          odoUnif 1 (2 * (M - 1)) (T - 1) (fun _ => y - 1))
    (htopple : ∀ s : ℕ, toppleTime 1 ((M - 1) - 1) ≤ (s : ℕ∞) →
      simplexMax 1 (M - 1) (fun z =>
        odoUnif 1 (2 * (M - 1)) (s + 2) z -
          odoUnif 1 (2 * (M - 1)) s z) ≤ 1)
    (hweak : ∀ (s : ℕ), 1 ≤ s → ∀ y : Site 1, y 0 = 1 →
      odoUnif 1 (2 * M) s y = odoUnif 1 (2 * M) s (y + unit 0) + 1 →
      odoUnif 1 (2 * M) (s + 1) y = odoUnif 1 (2 * M) s y)
    (htau : toppleTime 1 ((M - 1) - 1) + 2 ≤ toppleTime 1 (M - 1))
    (hcase_y_le_two : ∀ (z : Site 1), inSimplex 1 M z →
      2 ≤ odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z →
      (∀ y : ℤ, 3 ≤ y → y ≤ (M : ℤ) →
        ¬ (2 ≤ odoUnif 1 (2 * M) (T + 1) (fun _ => y) -
          odoUnif 1 (2 * M) (T - 1) (fun _ => y))) →
      (∀ (s : ℕ), 1 ≤ s → ∀ y : Site 1, y 0 = 1 →
        odoUnif 1 (2 * M) s y = odoUnif 1 (2 * M) s (y + unit 0) + 1 →
        odoUnif 1 (2 * M) (s + 1) y = odoUnif 1 (2 * M) s y) →
      toppleTime 1 ((M - 1) - 1) + 2 ≤ toppleTime 1 (M - 1) → False) :
    simplexMax 1 M (fun z =>
      odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z) ≤ 1 := by
  have hT2inf : (2 : ℕ∞) ≤ (T : ℕ∞) := by
    calc
      (2 : ℕ∞) = 0 + 2 := by norm_num
      _ ≤ toppleTime 1 ((M - 1) - 1) + 2 := by
        have hzero : (0 : ℕ∞) ≤ toppleTime 1 ((M - 1) - 1) := bot_le
        have hzero' := add_le_add_right hzero (2 : ℕ∞)
        simpa only [zero_add, add_zero, add_comm] using hzero'
      _ ≤ toppleTime 1 (M - 1) := htau
      _ = (T : ℕ∞) := hT
  have hT2 : 2 ≤ T := ENat.coe_le_coe.mp hT2inf
  have hM1 : 1 ≤ M := by omega
  have hlowtime : toppleTime 1 ((M - 1) - 1) ≤ ((T - 1 : ℕ) : ℕ∞) := by
    have hbound : toppleTime 1 ((M - 1) - 1) + 2 ≤ (T : ℕ∞) := by
      rw [← hT]
      exact htau
    have hfinite : toppleTime 1 ((M - 1) - 1) ≤ (T : ℕ∞) :=
      le_trans (le_add_right (le_refl _)) hbound
    obtain ⟨s, hs, _hst⟩ := (WithTop.le_coe_iff).mp hfinite
    rw [hs] at hbound ⊢
    have hbound' : ((s + 2 : ℕ) : ℕ∞) ≤ (T : ℕ∞) := by
      rw [ENat.coe_add]
      exact hbound
    have hst' : s + 2 ≤ T := ENat.coe_le_coe.mp hbound'
    exact WithTop.coe_le_coe.mpr (by omega)
  refine simplexMax_le 1 M _ 1 (by norm_num) ?_
  intro z hz
  by_cases hbad : 2 ≤ odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z
  · by_cases hlarge' : ∃ y : ℤ, 3 ≤ y ∧ y ≤ (M : ℤ) ∧
        2 ≤ odoUnif 1 (2 * M) (T + 1) (fun _ => y) -
          odoUnif 1 (2 * M) (T - 1) (fun _ => y)
    · obtain ⟨y, hy3, hyM, hyd⟩ := hlarge'
      have hyS : inSimplex 1 (M - 1) (fun _ : Fin 1 => y - 1) := by
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          change 1 ≤ y - 1 ∧ y - 1 ≤ (M - 1 : ℕ)
          constructor
          · omega
          · rw [Nat.cast_sub hM1]
            norm_num
            omega
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj]
      have hmax := htopple (T - 1) hlowtime
      rw [show (T - 1) + 2 = T + 1 by omega] at hmax
      have hle := le_simplexMax 1 (M - 1) (fun w =>
        odoUnif 1 (2 * (M - 1)) ((T - 1) + 2) w -
          odoUnif 1 (2 * (M - 1)) (T - 1) w) (fun _ => y - 1) hyS
      rw [show (T - 1) + 2 = T + 1 by omega] at hle
      have hcon := hconsist y hy3 hyM
      have hle' := le_trans hle hmax
      linarith
    · apply False.elim
      exact hcase_y_le_two z hz hbad (by
        intro y hy3 hyM hyd
        exact hlarge' ⟨y, hy3, hyM, hyd⟩) hweak htau
  · omega

theorem odo_one_strong_topple (M t : ℕ) (hM : 2 ≤ M)
    (ht : toppleTime 1 (M - 1) ≤ (t : ℕ∞))
    (hconsist : ∀ (T : ℕ), toppleTime 1 (M - 1) = (T : ℕ∞) → ∀ (y : ℤ),
      3 ≤ y → y ≤ (M : ℤ) →
      odoUnif 1 (2 * M) (T + 1) (fun _ => y) -
          odoUnif 1 (2 * M) (T - 1) (fun _ => y) =
        odoUnif 1 (2 * (M - 1)) (T + 1) (fun _ => y - 1) -
          odoUnif 1 (2 * (M - 1)) (T - 1) (fun _ => y - 1))
    (htopple : ∀ s : ℕ, toppleTime 1 ((M - 1) - 1) ≤ (s : ℕ∞) →
      simplexMax 1 (M - 1) (fun z =>
        odoUnif 1 (2 * (M - 1)) (s + 2) z -
          odoUnif 1 (2 * (M - 1)) s z) ≤ 1)
    (hweak : ∀ (s : ℕ), 1 ≤ s → ∀ y : Site 1, y 0 = 1 →
      odoUnif 1 (2 * M) s y = odoUnif 1 (2 * M) s (y + unit 0) + 1 →
      odoUnif 1 (2 * M) (s + 1) y = odoUnif 1 (2 * M) s y)
    (htau : toppleTime 1 ((M - 1) - 1) + 2 ≤ toppleTime 1 (M - 1))
    (hcase_y_le_two : ∀ (T : ℕ), toppleTime 1 (M - 1) = (T : ℕ∞) → ∀ (z : Site 1),
      inSimplex 1 M z →
      2 ≤ odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z →
      (∀ y : ℤ, 3 ≤ y → y ≤ (M : ℤ) →
        ¬ (2 ≤ odoUnif 1 (2 * M) (T + 1) (fun _ => y) -
          odoUnif 1 (2 * M) (T - 1) (fun _ => y))) →
      (∀ (s : ℕ), 1 ≤ s → ∀ y : Site 1, y 0 = 1 →
        odoUnif 1 (2 * M) s y = odoUnif 1 (2 * M) s (y + unit 0) + 1 →
        odoUnif 1 (2 * M) (s + 1) y = odoUnif 1 (2 * M) s y) →
      toppleTime 1 ((M - 1) - 1) + 2 ≤ toppleTime 1 (M - 1) → False) :
    simplexMax 1 M (fun z =>
      odoUnif 1 (2 * M) (t + 2) z - odoUnif 1 (2 * M) t z) ≤ 1 := by
  obtain ⟨T, hT, hTt⟩ := (WithTop.le_coe_iff).mp ht
  have hbase := odo_one_strong_topple_at M hM T hT
    (hconsist T hT) htopple hweak htau (hcase_y_le_two T hT)
  have hlimit := Frozen.topple_limit 1 M (by norm_num) (by omega) (fun _ => 2)
    (fun _ _ _ _ => rfl) T t 2 hTt
  simp only [Corrected.maximum_eq_simplexMax] at hlimit
  exact le_trans hlimit hbase

end DimRed
