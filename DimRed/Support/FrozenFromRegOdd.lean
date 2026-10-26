module

public import DimRed.Support.NonnegativeUpdate
public import DimRed.Support.RegInduction
public import DimRed.Support.StrongDerivRaw
public import DimRed.Support.SelfSimilarityMain

@[expose] public section

/-!
# The odd cube against the even cube

For `N + 1 = 2 M` the cube `C_N^{(d)}` is the cube `C_{2M}^{(d)}` with the layer `x_i = 1 - M`
removed.  On the positive orthant `{1, …, M}^d` the two parallel toppling odometers agree at every
time, provided weak facet compatibility holds at side `M` and dimension `d`: the two recursions
differ only at a site with a coordinate equal to `1`, where the lower neighbour is the site itself
in the even cube and the upper neighbour in the odd cube, and weak facet compatibility says that
when these two values differ the site does not topple.  This is the boundary adjustment for odd
`N` that `dimred-corrected-arxiv.tex`, label `subsec:symmetry` leaves to the reader.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

open LatticeProb

namespace DimRed

theorem loCoord_of_succ_eq_two_mul {N M : ℕ} (hN : N + 1 = 2 * M) : loCoord N = 2 - (M : ℤ) := by
  simp only [loCoord]
  omega

theorem hiCoord_of_succ_eq_two_mul {N M : ℕ} (hN : N + 1 = 2 * M) : hiCoord N = (M : ℤ) := by
  simp only [hiCoord, sideHalf]
  omega

/-- The odometer on the odd cube of side `2 M - 1` agrees with the odometer on the even cube of
side `2 M` on the region `x ≥ 1`, at every time. -/
theorem odoUnif_odd_eq_even (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hW : ∀ t, RegWeak d M t) (N : ℕ) (hN : N + 1 = 2 * M) :
    ∀ t : ℕ, ∀ x : Site d, (∀ i, 1 ≤ x i) →
      odoUnif d N t x = odoUnif d (2 * M) t x := by
  have hNodd : N % 2 = 1 := by omega
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  intro t
  induction t with
  | zero =>
    intro x _
    simp [odoUnif, odo]
  | succ t ih =>
    intro x hx1
    by_cases hxM : ∀ i, x i ≤ (M : ℤ)
    · have hxp : inPos d M x := fun i => ⟨hx1 i, hxM i⟩
      have hvc : inCube d (2 * M) x := inPos_inCube hxp
      have hwc : inCube d N x := by
        intro i
        rw [loCoord_of_succ_eq_two_mul hN, hiCoord_of_succ_eq_two_mul hN]
        exact ⟨by have := hx1 i; omega, hxM i⟩
      have hv : odoUnif d (2 * M) (t + 1) x
          = (2 * (d : ℤ) + nbrSum (odoUnif d (2 * M) t) x) / (2 * (d : ℤ)) :=
        DimRed.bounded_point_update d (2 * M) hd (fun _ => 2 * (d : ℤ))
          (fun _ _ => by positivity) (fun _ _ => by linarith) t x hvc
      have hw : odoUnif d N (t + 1) x
          = (2 * (d : ℤ) + nbrSum (odoUnif d N t) x) / (2 * (d : ℤ)) :=
        DimRed.bounded_point_update d N hd (fun _ => 2 * (d : ℤ))
          (fun _ _ => by positivity) (fun _ _ => by linarith) t x hwc
      have hpos_add : ∀ i : Fin d, ∀ k : Fin d, 1 ≤ (x + unit i) k := by
        intro i k
        rw [add_unit_apply]
        have := hx1 k
        split <;> omega
      have hplus : ∀ i : Fin d, odoUnif d N t (x + unit i) = odoUnif d (2 * M) t (x + unit i) :=
        fun i => ih _ (hpos_add i)
      have hminus_ge : ∀ i : Fin d, 2 ≤ x i →
          odoUnif d N t (x - unit i) = odoUnif d (2 * M) t (x - unit i) := by
        intro i hi
        refine ih _ (fun k => ?_)
        rw [sub_unit_apply]
        have := hx1 k
        split_ifs with hk
        · subst hk; omega
        · omega
      have hrefl : ∀ i : Fin d, x i = 1 →
          odoUnif d N t (x - unit i) = odoUnif d N t (x + unit i) := by
        intro i hi
        have h := odo_reflect_coord_odd d N hNodd (2 * (d : ℤ)) t (x - unit i) i
        have e : (fun k => if k = i then 2 - (x - unit i) i else (x - unit i) k)
            = x + unit i := by
          funext k
          by_cases hk : k = i
          · subst hk
            simp only [ite_true, sub_unit_apply, add_unit_apply]
            omega
          · simp only [ite_eq_right hk, sub_unit_apply, add_unit_apply]
            omega
        rw [e] at h
        exact h.symm
      have hvrefl : ∀ i : Fin d, x i = 1 →
          odoUnif d (2 * M) t (x - unit i) = odoUnif d (2 * M) t x :=
        fun i hi => odo_sub_unit_of_one d M (2 * (d : ℤ)) t x i hi
      have hax : ∀ i : Fin d, x i = 1 →
          odoUnif d (2 * M) t (x + unit i) ≤ odoUnif d (2 * M) t x :=
        fun i hi => odo_axis_refl d M hd (2 * (d : ℤ)) (by positivity) (by linarith) t x i
          (by omega)
      have hfd : ∀ i : Fin d, x i = 1 →
          odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit i) ≤ 1 := by
        intro i hi
        have h := odo_first_diff d M hd (by omega) t i x (by omega)
        rw [hi] at h
        exact h
      have hminus_le : ∀ i : Fin d,
          odoUnif d N t (x - unit i) ≤ odoUnif d (2 * M) t (x - unit i) := by
        intro i
        rcases (by have := hx1 i; omega : x i = 1 ∨ 2 ≤ x i) with hi | hi
        · rw [hrefl i hi, hplus i, hvrefl i hi]
          exact hax i hi
        · rw [hminus_ge i hi]
      have hle : nbrSum (odoUnif d N t) x ≤ nbrSum (odoUnif d (2 * M) t) x := by
        unfold nbrSum
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := hplus i
        have h2 := hminus_le i
        linarith
      have hup : odoUnif d N (t + 1) x ≤ odoUnif d (2 * M) (t + 1) x := by
        rw [hw, hv]
        exact Int.ediv_le_ediv hdpos (by linarith)
      by_cases hA : ∀ i : Fin d, x i = 1 →
          odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit i)
      · have heq : nbrSum (odoUnif d N t) x = nbrSum (odoUnif d (2 * M) t) x := by
          unfold nbrSum
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hplus i]
          rcases (by have := hx1 i; omega : x i = 1 ∨ 2 ≤ x i) with hi | hi
          · rw [hrefl i hi, hplus i, hvrefl i hi, ← hA i hi]
          · rw [hminus_ge i hi]
        rw [hw, hv, heq]
      · push Not at hA
        obtain ⟨k, hk1, hkne⟩ := hA
        have hk_ge := hax k hk1
        have hk_le := hfd k hk1
        have hgap : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1 := by
          omega
        have ht1 : 1 ≤ t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · subst h0
            simp [odoUnif, odo] at hgap
          · exact h0
        have hstay := weak_raw d M t ht1 (hW t) x hxp k hk1 hgap
        have hlow : odoUnif d N t x ≤ odoUnif d N (t + 1) x :=
          odo_mono d N (fun _ => 2 * (d : ℤ)) (Nat.le_succ t) x
        have hwt : odoUnif d N t x = odoUnif d (2 * M) t x := ih x hx1
        omega
    · push Not at hxM
      obtain ⟨i, hi⟩ := hxM
      have hvo : ¬ inCube d (2 * M) x := by
        intro h
        have := (h i).2
        rw [hiCoord_two_mul] at this
        omega
      have hwo : ¬ inCube d N x := by
        intro h
        have := (h i).2
        rw [hiCoord_of_succ_eq_two_mul hN] at this
        omega
      rw [show odoUnif d N (t + 1) x = 0 from odo_eq_zero_outside d N _ (t + 1) x hwo,
        show odoUnif d (2 * M) (t + 1) x = 0 from
          odo_eq_zero_outside d (2 * M) _ (t + 1) x hvo]

/-- The odometer at the all-ones point of the cubes of side `1` and `2` (`M = 1`) is at most `1`
at every time, and equals `1` after one step. -/
theorem odoUnif_ones_succ (d N : ℕ) (hd : 1 ≤ d) (hN : N = 1 ∨ N = 2) (t : ℕ)
    (h0 : 0 ≤ odoUnif d N t (fun _ => 1)) (h1 : odoUnif d N t (fun _ => 1) ≤ 1) :
    odoUnif d N (t + 1) (fun _ => 1) = 1 := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hc : inCube d N (fun _ => (1 : ℤ)) := by
    intro i
    rcases hN with rfl | rfl <;> simp [loCoord, hiCoord, sideHalf]
  have hrec : odoUnif d N (t + 1) (fun _ => 1)
      = (2 * (d : ℤ) + nbrSum (odoUnif d N t) (fun _ => 1)) / (2 * (d : ℤ)) :=
    DimRed.bounded_point_update d N hd (fun _ => 2 * (d : ℤ))
      (fun _ _ => by positivity) (fun _ _ => by linarith) t _ hc
  have hplus : ∀ i : Fin d, odoUnif d N t ((fun _ => (1 : ℤ)) + unit i) = 0 := by
    intro i
    refine odo_eq_zero_outside d N _ t _ ?_
    intro h
    have h2 := (h i).2
    rw [add_unit_apply] at h2
    rcases hN with rfl | rfl <;> simp [hiCoord, sideHalf] at h2
  have hminus : ∀ i : Fin d, odoUnif d N t ((fun _ => (1 : ℤ)) - unit i)
      = if N = 1 then 0 else odoUnif d N t (fun _ => 1) := by
    intro i
    rcases hN with rfl | rfl
    · rw [ite_eq_left rfl]
      refine odo_eq_zero_outside d 1 _ t _ ?_
      intro h
      have h2 := (h i).1
      rw [sub_unit_apply] at h2
      simp [loCoord] at h2
    · rw [ite_eq_right (by norm_num)]
      have h := odo_sub_unit_of_one d 1 (2 * (d : ℤ)) t (fun _ => (1 : ℤ)) i rfl
      simp only [Nat.mul_one] at h
      exact h
  have hsum : nbrSum (odoUnif d N t) (fun _ => 1)
      = (d : ℤ) * (if N = 1 then 0 else odoUnif d N t (fun _ => 1)) := by
    unfold nbrSum
    rw [Finset.sum_congr rfl (fun i _ => by rw [hplus i, hminus i, zero_add])]
    simp
  rw [hrec, hsum]
  apply ediv_unique hdpos
  · rcases hN with rfl | rfl
    · simp
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ite_false]
      nlinarith
  · rcases hN with rfl | rfl
    · simp; linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ite_false]
      nlinarith

theorem odoUnif_ones_le (d N : ℕ) (hd : 1 ≤ d) (hN : N = 1 ∨ N = 2) :
    ∀ t : ℕ, odoUnif d N t (fun _ => 1) ≤ 1 := by
  intro t
  induction t with
  | zero => simp [odoUnif, odo]
  | succ t ih =>
    rw [odoUnif_ones_succ d N hd hN t (odo_nonneg d N _ t _) ih]

theorem odoUnif_ones_eq_one (d N : ℕ) (hd : 1 ≤ d) (hN : N = 1 ∨ N = 2) (t : ℕ) (ht : 1 ≤ t) :
    odoUnif d N t (fun _ => 1) = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact odoUnif_ones_succ d N hd hN s (odo_nonneg d N _ s _) (odoUnif_ones_le d N hd hN s)

end DimRed
