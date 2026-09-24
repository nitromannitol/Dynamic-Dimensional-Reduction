/-
Elementary lemmas for the difference comparison of `dimred.tex:473-492`: the
shift and subtraction identities for the neighbour sum, the fact that a point
of the sorted fundamental domain lies in the hypercube, and the floor-division
bounds that turn a bound on a neighbour sum into a bound on the odometer.
-/
import DimRed.Support.Recursion

namespace DimRed

open LatticeProb

/-- Shifting the argument of `u` shifts the neighbour sum. -/
theorem nbrSum_shift {d : ℕ} (u : Site d → ℤ) (x w : Site d) :
    nbrSum (fun y => u (y + w)) x = nbrSum u (x + w) := by
  simp only [nbrSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1 <;> abel

/-- The neighbour sum is additive. -/
theorem nbrSum_sub {d : ℕ} (u v : Site d → ℤ) (x : Site d) :
    nbrSum (fun y => u y - v y) x = nbrSum u x - nbrSum v x := by
  simp only [nbrSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A point of the sorted fundamental domain lies in the hypercube. -/
theorem inSimplex_inCube (d M : ℕ) (x : Site d) (hx : inSimplex d M x) :
    inCube d (2 * M) x := by
  intro i
  obtain ⟨h1, h2⟩ := hx.1 i
  constructor
  · simp only [loCoord]
    omega
  · simp only [hiCoord, sideHalf]
    omega

/-- The difference of two floor divisions is bounded by the floor division of
the difference plus `m - 1`. -/
theorem ediv_sub_ediv_le (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    a / (m : ℤ) - b / (m : ℤ) ≤ (a - b + (m : ℤ) - 1) / (m : ℤ) := by
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hQ : a - b + (m : ℤ) - 1 < ((a - b + (m : ℤ) - 1) / (m : ℤ) + 1) * (m : ℤ) :=
    Int.lt_ediv_add_one_mul_self _ hmz
  have hQ2 : a - b ≤ (a - b + (m : ℤ) - 1) / (m : ℤ) * (m : ℤ) := by linarith
  have hB : b < (b / (m : ℤ) + 1) * (m : ℤ) := Int.lt_ediv_add_one_mul_self _ hmz
  have hB2 : b ≤ b / (m : ℤ) * (m : ℤ) + (m : ℤ) - 1 := by linarith
  have hkey : a < ((a - b + (m : ℤ) - 1) / (m : ℤ) + b / (m : ℤ) + 1) * (m : ℤ) := by
    have hp : ((a - b + (m : ℤ) - 1) / (m : ℤ) + b / (m : ℤ) + 1) * (m : ℤ)
        = (a - b + (m : ℤ) - 1) / (m : ℤ) * (m : ℤ) + b / (m : ℤ) * (m : ℤ) + (m : ℤ) := by
      ring
    rw [hp]
    linarith
  have hfinal : a / (m : ℤ) < (a - b + (m : ℤ) - 1) / (m : ℤ) + b / (m : ℤ) + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hmz]
    exact hkey
  linarith

/-- `⌊(a + m - 1)/m⌋ ≤ g` when `a ≤ m g`. -/
theorem ediv_le_of_le_mul (a g : ℤ) (m : ℕ) (hm : 0 < m) (h : a ≤ (m : ℤ) * g) :
    (a + (m : ℤ) - 1) / (m : ℤ) ≤ g := by
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hmz]
  nlinarith

/-- `⌊(m g + m - 1)/m⌋ ≤ g`. -/
theorem ediv_mul_le_self (g : ℤ) (m : ℕ) (hm : 0 < m) :
    ((m : ℤ) * g + (m : ℤ) - 1) / (m : ℤ) ≤ g := by
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hmz]
  nlinarith

/-- The `i`-th coordinate of the unit vector `unit i` is `1`. -/
theorem unit_apply_self {d : ℕ} (i : Fin d) : unit i i = 1 := by
  simp [unit, Pi.single_eq_same]

/-- The `j`-th coordinate of `unit i` is `0` for `j ≠ i`. -/
theorem unit_apply_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) : unit i j = 0 := by
  simp [unit, Pi.single_eq_of_ne h]

/-- A unit vector is nonzero. -/
theorem unit_ne_zero' {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- A strictly interior point of the sorted fundamental domain stays in it after
a unit step. -/
theorem inSimplex_add_unit (d M : ℕ) (x : Site d) (hx : inSimplex d M x)
    (hM : ∀ i : Fin d, x i < (M : ℤ)) (_h1 : ∀ i : Fin d, 1 < x i)
    (hdec : ∀ i j : Fin d, i < j → x j < x i) (i : Fin d) :
    inSimplex d M (x + unit i) := by
  have hval : ∀ k : Fin d, (x + unit i) k = if k = i then x k + 1 else x k := by
    intro k
    by_cases h : k = i
    · rw [h, if_pos rfl]
      simp [Pi.add_apply, unit, Pi.single_eq_same]
    · rw [if_neg h]
      simp only [Pi.add_apply, unit, Pi.single_eq_of_ne h]
      ring
  constructor
  · intro k
    rw [hval k]
    by_cases h : k = i
    · rw [if_pos h]
      have hk := hx.1 k
      have hkM := hM k
      omega
    · rw [if_neg h]
      exact hx.1 k
  · intro a b hab
    rw [hval a, hval b]
    by_cases ha : a = i
    · by_cases hb : b = i
      · rw [if_pos ha, if_pos hb]
        have := hx.2 a b hab
        omega
      · rw [if_pos ha, if_neg hb]
        have hlt : a < b := lt_of_le_of_ne hab (by rw [ha]; exact Ne.symm hb)
        have := hdec a b hlt
        omega
    · by_cases hb : b = i
      · rw [if_neg ha, if_pos hb]
        have hlt : a < b := lt_of_le_of_ne hab (by rw [hb]; exact ha)
        have := hdec a b hlt
        omega
      · rw [if_neg ha, if_neg hb]
        exact hx.2 a b hab

/-- A strictly interior point of the sorted fundamental domain stays in it after
a negative unit step. -/
theorem inSimplex_sub_unit (d M : ℕ) (x : Site d) (hx : inSimplex d M x)
    (_hM : ∀ i : Fin d, x i < (M : ℤ)) (h1 : ∀ i : Fin d, 1 < x i)
    (hdec : ∀ i j : Fin d, i < j → x j < x i) (i : Fin d) :
    inSimplex d M (x - unit i) := by
  have hval : ∀ k : Fin d, (x - unit i) k = if k = i then x k - 1 else x k := by
    intro k
    by_cases h : k = i
    · rw [h, if_pos rfl]
      simp [Pi.sub_apply, unit]
    · rw [if_neg h]
      simp [Pi.sub_apply, unit, h]
  constructor
  · intro k
    rw [hval k]
    by_cases h : k = i
    · rw [if_pos h]
      have hk := hx.1 k
      have hk1 := h1 k
      omega
    · rw [if_neg h]
      exact hx.1 k
  · intro a b hab
    rw [hval a, hval b]
    by_cases ha : a = i
    · by_cases hb : b = i
      · rw [if_pos ha, if_pos hb]
        have := hx.2 a b hab
        omega
      · rw [if_pos ha, if_neg hb]
        have hlt : a < b := lt_of_le_of_ne hab (fun h => hb (h.symm.trans ha))
        have := hdec a b hlt
        omega
    · by_cases hb : b = i
      · rw [if_neg ha, if_pos hb]
        have hlt : a < b := lt_of_le_of_ne hab (fun h => ha (h.trans hb))
        have := hdec a b hlt
        omega
      · rw [if_neg ha, if_neg hb]
        exact hx.2 a b hab

/-- A point which is not on any of the three boundaries is strictly interior. -/
theorem not_bdry_strict {d : ℕ} (M : ℕ) (w x : Site d) (h : ¬ bdry M w x) :
    (∀ i : Fin d, (x + w) i < (M : ℤ)) ∧ (∀ i : Fin d, 1 < (x + w) i) ∧
      (∀ i j : Fin d, i < j → (x + w) j < (x + w) i) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · by_contra hc
    exact h (Or.inl ⟨i, not_lt.mp hc⟩)
  · by_contra hc
    exact h (Or.inr (Or.inl ⟨i, not_lt.mp hc⟩))
  · by_contra hc
    exact h (Or.inr (Or.inr ⟨i, j, hij, not_lt.mp hc⟩))

/-- A strictly interior point of the box lies in the sorted fundamental domain. -/
theorem inSimplex_of_strict {d : ℕ} (M : ℕ) (x : Site d)
    (hM : ∀ i : Fin d, x i < (M : ℤ)) (h1 : ∀ i : Fin d, 1 < x i)
    (hdec : ∀ i j : Fin d, i < j → x j < x i) : inSimplex d M x := by
  refine ⟨fun i => ⟨le_of_lt (h1 i), le_of_lt (hM i)⟩, fun i j hij => ?_⟩
  rcases eq_or_lt_of_le hij with h | h
  · rw [← h]
  · exact le_of_lt (hdec i j h)

end DimRed
