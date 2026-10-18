/-
# Signed parabolic least action

The parabolic least-action comparison from arXiv:2009.05968v2,
`main.tex:300-333` (Lemma `parabolic_comparison`), with the signed initial
piles allowed by the subsection's upper-bound-only standing assumption.
-/
import DimRed.Support.SignedUpdate

open LatticeProb

namespace DimRed

private theorem odo_nonneg (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ odo d N s₀ t x := by
  induction t with
  | zero => simp [odo]
  | succ t ih =>
      have hstep := odo_succ_sub_bounds d N s₀ t x
      omega

private theorem nbrSum_nonneg {d : ℕ} (f : Site d → ℤ)
    (hf : ∀ y, 0 ≤ f y) (x : Site d) : 0 ≤ nbrSum f x := by
  unfold nbrSum
  apply Finset.sum_nonneg
  intro i hi
  exact add_nonneg (hf _) (hf _)

/-- At a site which has toppled, the current pile is nonnegative, even when
the initial pile is signed. -/
private theorem sandp_nonneg_of_odo_pos (d N : ℕ) (s₀ : Site d → ℤ)
    (t : ℕ) (x : Site d) (hodo : 0 < odo d N s₀ t x) :
    0 ≤ sandp d N s₀ t x := by
  induction t with
  | zero => simp [odo] at hodo
  | succ t ih =>
      by_cases hx : inCube d N x
      · have htop := odo_succ_sub_eq d N s₀ t x hx
        have hupdate := sandp_succ d N s₀ t x
        rw [lap] at hupdate
        have hdelta_nonneg : ∀ y,
            0 ≤ odo d N s₀ (t + 1) y - odo d N s₀ t y :=
          fun y => (odo_succ_sub_bounds d N s₀ t y).1
        have hneighbors := nbrSum_nonneg
          (fun y => odo d N s₀ (t + 1) y - odo d N s₀ t y)
          hdelta_nonneg x
        by_cases hfire : 2 * (d : ℤ) ≤ sandp d N s₀ t x
        · have hdelta :
              odo d N s₀ (t + 1) x - odo d N s₀ t x = 1 := by
            rw [htop, if_pos hfire]
          rw [hdelta] at hupdate
          nlinarith [hupdate, hneighbors]
        · have hdelta :
              odo d N s₀ (t + 1) x - odo d N s₀ t x = 0 := by
            rw [htop, if_neg hfire]
          have hprev : 0 < odo d N s₀ t x := by
            have heq : odo d N s₀ (t + 1) x = odo d N s₀ t x :=
              sub_eq_zero.mp hdelta
            rw [heq] at hodo
            exact hodo
          have hprevPile := ih hprev
          rw [hdelta] at hupdate
          linarith [hupdate, hneighbors, hprevPile]
      · have hout := odo_eq_zero_outside d N s₀ (t + 1) x hx
        rw [hout] at hodo
        omega

private theorem signed_odometer_parabolic_feasible
    (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs₁ : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    ∀ (t : ℕ) (x : Site d), inCube d N x →
      (-(2 * (d : ℤ)) * odo d N s₀ (t + 1) x + nbrSum (odo d N s₀ t) x) + s₀ x
        ≤ 2 * (d : ℤ) - 1 := by
  intro t x hx
  have hden : (0 : ℤ) < 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  have hstep := odo_succ_eq_max_quotient d N hd s₀ hs₁ t x hx
  have hquot :
      (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
        ≤ odo d N s₀ (t + 1) x := by
    rw [hstep]
    exact le_max_right _ _
  have hquot_lt :
      (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
        < odo d N s₀ (t + 1) x + 1 := by omega
  have hsum_lt :
      s₀ x + nbrSum (odo d N s₀ t) x
        < (odo d N s₀ (t + 1) x + 1) * (2 * (d : ℤ)) := by
    have h := (Int.ediv_lt_iff_lt_mul hden).1 hquot_lt
    nlinarith [h]
  nlinarith [hsum_lt]

/-- The odometer satisfies the parabolic constraint and is pointwise below
every nonnegative, zero-extended trajectory satisfying that constraint.
There is no lower bound on the initial pile. -/
theorem signed_parabolic_least_action (d N : ℕ) (hd : 1 ≤ d)
    (s₀ : Site d → ℤ)
    (hs₁ : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    (∀ (t : ℕ) (x : Site d), inCube d N x →
        (-(2 * (d : ℤ)) * odo d N s₀ (t + 1) x + nbrSum (odo d N s₀ t) x) + s₀ x
          ≤ 2 * (d : ℤ) - 1) ∧
      ∀ u : ℕ → Site d → ℤ, (∀ t y, 0 ≤ u t y) →
        (∀ t y, ¬ inCube d N y → u t y = 0) →
        (∀ (t : ℕ) (y : Site d), inCube d N y →
            (-(2 * (d : ℤ)) * u (t + 1) y + nbrSum (u t) y) + s₀ y
              ≤ 2 * (d : ℤ) - 1) →
        ∀ (t : ℕ) (y : Site d), odo d N s₀ t y ≤ u t y := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  constructor
  · exact signed_odometer_parabolic_feasible d N hd s₀ hs₁
  · intro u hu_nonneg hu_outside hu_feasible t
    induction t with
    | zero =>
        intro y
        simpa [odo] using hu_nonneg 0 y
    | succ t ih =>
        intro y
        by_cases hy : inCube d N y
        · have hstep := odo_succ_eq_max_quotient d N hd s₀ hs₁ t y hy
          have hneighbors := nbrSum_mono ih y
          have hstrict :
              s₀ y + nbrSum (u t) y
                < (u (t + 1) y + 1) * (2 * (d : ℤ)) := by
            nlinarith [hu_feasible t y hy]
          have hquot_u :
              (s₀ y + nbrSum (u t) y) / (2 * (d : ℤ))
                ≤ u (t + 1) y := by
            have hlt :
                (s₀ y + nbrSum (u t) y) / (2 * (d : ℤ))
                  < u (t + 1) y + 1 := by
              apply (Int.ediv_lt_iff_lt_mul hdpos).2
              nlinarith [hstrict]
            omega
          have hquot_odo :
              (s₀ y + nbrSum (odo d N s₀ t) y) / (2 * (d : ℤ))
                ≤ u (t + 1) y := by
            have hnum :
                s₀ y + nbrSum (odo d N s₀ t) y
                  ≤ s₀ y + nbrSum (u t) y := by linarith [hneighbors]
            have hquot_mono := Int.ediv_le_ediv hdpos hnum
            exact le_trans hquot_mono hquot_u
          have hprev : odo d N s₀ t y ≤ u (t + 1) y := by
            by_cases hzero : odo d N s₀ t y = 0
            · rw [hzero]
              exact hu_nonneg (t + 1) y
            · have hpos : 0 < odo d N s₀ t y := by
                have hnonneg := odo_nonneg d N s₀ t y
                omega
              have hpile := sandp_nonneg_of_odo_pos d N s₀ t y hpos
              have hbase :
                  s₀ y + nbrSum (odo d N s₀ t) y =
                    sandp d N s₀ t y + (2 * (d : ℤ)) * odo d N s₀ t y := by
                simp only [sandp, lap]
                ring
              have hprev_quot :
                  odo d N s₀ t y ≤
                    (s₀ y + nbrSum (odo d N s₀ t) y) / (2 * (d : ℤ)) := by
                apply (Int.le_ediv_iff_mul_le hdpos).2
                rw [mul_comm, hbase]
                nlinarith [hpile]
              exact le_trans hprev_quot hquot_odo
          rw [hstep]
          exact max_le hprev hquot_odo
        · rw [odo_eq_zero_outside d N s₀ (t + 1) y hy]
          exact hu_nonneg (t + 1) y

private def negativePileExample : Site 1 → ℤ := fun _ => -1

private def zeroTrajectoryExample : ℕ → Site 1 → ℤ := fun _ _ => 0

/-- A concrete signed instance: the pile `s₀ ≡ -1` admits the zero feasible
trajectory, and its odometer is exactly that pointwise minimum. -/
example :
    (∀ y, inCube 1 1 y → negativePileExample y ≤ 3) ∧
      (∀ t x, inCube 1 1 x →
        (-(2 : ℤ) * zeroTrajectoryExample (t + 1) x +
          nbrSum (zeroTrajectoryExample t) x) + negativePileExample x ≤ 1) ∧
      (∀ t x, odo 1 1 negativePileExample t x = 0) ∧
      (∀ t x, inCube 1 1 x →
        (-(2 : ℤ) * odo 1 1 negativePileExample (t + 1) x +
          nbrSum (odo 1 1 negativePileExample t) x) + negativePileExample x ≤ 1) := by
  have hupper : ∀ y, inCube 1 1 y → negativePileExample y ≤ 3 := by
    intro y hy
    norm_num [negativePileExample]
  have hu_feasible : ∀ t x, inCube 1 1 x →
      (-(2 : ℤ) * zeroTrajectoryExample (t + 1) x +
        nbrSum (zeroTrajectoryExample t) x) + negativePileExample x ≤ 1 := by
    intro t x hx
    simp [negativePileExample, zeroTrajectoryExample, nbrSum]
  have hleast := signed_parabolic_least_action 1 1 (by norm_num)
    negativePileExample hupper
  have hdom := hleast.2 zeroTrajectoryExample
    (by intro t y; simp [zeroTrajectoryExample])
    (by intro t y hy; simp [zeroTrajectoryExample]) hu_feasible
  refine ⟨hupper, hu_feasible, ?_, hleast.1⟩
  intro t x
  apply le_antisymm
  · simpa [zeroTrajectoryExample] using hdom t x
  · exact odo_nonneg 1 1 negativePileExample t x

end DimRed
