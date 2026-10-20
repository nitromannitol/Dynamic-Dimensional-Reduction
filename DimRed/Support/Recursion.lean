/-
The two displays of the subsection labelled `subsec:main_result` in `dimred-corrected-arxiv.tex` as theorems about `DimRed.odo`, the
invariant `0 ≤ s_t ≤ 2(2d) - 1` that the paper's blanket hypothesis
`s_0 ≤ 2(2d) - 1` propagates in time, and the elementary consequences of the
recursion used everywhere below.
-/
import DimRed.Support.Basic

namespace DimRed

open LatticeProb

variable {d N : ℕ} {s₀ : Site d → ℤ}

/-- The odometer vanishes off the hypercube. -/
theorem odo_eq_zero_outside (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d)
    (hx : ¬ inCube d N x) : odo d N s₀ t x = 0 := by
  induction t with
  | zero => rfl
  | succ n _ => simp only [odo, if_neg hx]

/-- A site topples at most once per time step. -/
theorem odo_succ_sub_bounds (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ odo d N s₀ (t + 1) x - odo d N s₀ t x ∧
      odo d N s₀ (t + 1) x - odo d N s₀ t x ≤ 1 := by
  by_cases hx : inCube d N x
  · simp only [odo, if_pos hx]
    split <;> omega
  · rw [odo_eq_zero_outside d N s₀ (t + 1) x hx, odo_eq_zero_outside d N s₀ t x hx]
    omega

/-- `∑_{y ∼ x} u(y)` for a `{0,1}`-valued `u` lies between `0` and `2d`. -/
theorem nbrSum_bounds {d : ℕ} (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y ∧ u y ≤ 1) (x : Site d) :
    0 ≤ nbrSum u x ∧ nbrSum u x ≤ 2 * (d : ℤ) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => by
      have h1 := (hu (x + unit i)).1
      have h2 := (hu (x - unit i)).1
      linarith
  · calc nbrSum u x ≤ ∑ _i : Fin d, (2 : ℤ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := (hu (x + unit i)).2
          have h2 := (hu (x - unit i)).2
          linarith
      _ = 2 * (d : ℤ) := by simp [Finset.sum_const, Finset.card_univ]; ring

/-- `Δ` is additive in its argument. -/
theorem lap_sub {d : ℕ} (f g : Site d → ℤ) (x : Site d) :
    lap (fun y => f y - g y) x = lap f x - lap g x := by
  simp only [lap, nbrSum]; simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring

/-- The quotient of the floor division `a / b` is characterised by the two
inequalities `b q ≤ a < b (q+1)`. -/
theorem ediv_unique {a b q : ℤ} (hb : 0 < b) (h1 : b * q ≤ a) (h2 : a < b * (q + 1)) :
    a / b = q := by
  have hle : q ≤ a / b := (Int.le_ediv_iff_mul_le hb).2 (by rw [mul_comm]; exact h1)
  have hlt : a / b < q + 1 := (Int.ediv_lt_iff_lt_mul hb).2 (by rw [mul_comm]; exact h2)
  omega

/-- `∑_{y ∼ x}` is monotone. -/
theorem nbrSum_mono {d : ℕ} {u v : Site d → ℤ} (h : ∀ y, u y ≤ v y) (x : Site d) :
    nbrSum u x ≤ nbrSum v x := by
  simp only [nbrSum]; refine Finset.sum_le_sum fun i _ => ?_
  have h1 := h (x + unit i); have h2 := h (x - unit i); linarith

/-- `s_0` is the initial sandpile. -/
theorem sandp_zero (d N : ℕ) (s₀ : Site d → ℤ) (x : Site d) :
    sandp d N s₀ 0 x = s₀ x := by
  simp [sandp, lap, nbrSum, odo]

/-- A site of the hypercube topples at step `t` exactly when it is unstable. -/
theorem odo_succ_sub_eq (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x - odo d N s₀ t x
      = if 2 * (d : ℤ) ≤ sandp d N s₀ t x then 1 else 0 := by
  simp only [odo, if_pos hx, sandp]; ring_nf

/-- The paper's second display, `s_{t+1} = s_t + Δ(v_{t+1} - v_t)`. -/
theorem sandp_succ (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) :
    sandp d N s₀ (t + 1) x
      = sandp d N s₀ t x + lap (fun y => odo d N s₀ (t + 1) y - odo d N s₀ t y) x := by
  rw [lap_sub]; simp only [sandp]; ring

/-- The paper's first display, `v_{t+1} = v_t + 1{s_t ≥ 2d}`. -/
theorem odo_succ_eq (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x
      = odo d N s₀ t x + (if 2 * (d : ℤ) ≤ sandp d N s₀ t x then 1 else 0) := by
  have := odo_succ_sub_eq d N s₀ t x hx; linarith

/-- The invariant of the parallel toppling process: the blanket hypothesis
`0 ≤ s_0 ≤ 2(2d) - 1` of the subsection labelled `subsec:notation` in `dimred-corrected-arxiv.tex` propagates in time. -/
theorem sandp_bounds (d N : ℕ) (s₀ : Site d → ℤ)
    (h0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (h1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    0 ≤ sandp d N s₀ t x ∧ sandp d N s₀ t x ≤ 2 * (2 * (d : ℤ)) - 1 := by
  induction t with
  | zero => rw [sandp_zero]; exact ⟨h0 x hx, h1 x hx⟩
  | succ n ih =>
    have hnb := nbrSum_bounds (fun y => odo d N s₀ (n + 1) y - odo d N s₀ n y)
      (fun y => odo_succ_sub_bounds d N s₀ n y) x
    have hstep := sandp_succ d N s₀ n x
    have hdel := odo_succ_sub_eq d N s₀ n x hx
    rw [lap] at hstep
    split at hdel
    · rename_i hcase
      rw [hstep, hdel]
      constructor <;> linarith [ih.1, ih.2, hnb.1, hnb.2]
    · rename_i hcase
      rw [not_le] at hcase
      rw [hstep, hdel]
      constructor <;> linarith [ih.1, ih.2, hnb.1, hnb.2]

end DimRed
