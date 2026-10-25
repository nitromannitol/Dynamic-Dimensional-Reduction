module

public import DimRed.Support.Case2FirstWait
public import DimRed.Support.OneDimTerminal

@[expose] public section

/-!
# The quadratic barrier for the uniform even-cube odometer

The reflected one dimensional quadratic profile is lifted along one coordinate
and set to zero off the physical cube. Its directed neighbor sum is a strict
supersolution for the actual floor update, giving an all-time bound for the
simultaneous odometer in every dimension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- `U_M(z) = (M(M+1)-z(z-1))/2` on the positive half of the even cube. -/
def case2QuadraticValue (M : ℕ) (z : ℤ) : ℤ := onePoly M z / 2

/-- The two points on the reflecting face have exactly the same profile value. -/
theorem case2_quadratic_value_reflect (M : ℕ) :
    case2QuadraticValue M 0 = case2QuadraticValue M 1 := by
  simp [case2QuadraticValue, onePoly]

/-- The profile vanishes at the first point beyond the dissipating face. -/
theorem case2_quadratic_value_dissipate (M : ℕ) :
    case2QuadraticValue M ((M : ℤ) + 1) = 0 := by
  unfold case2QuadraticValue onePoly
  rw [show (M : ℤ) * ((M : ℤ) + 1) -
      ((M : ℤ) + 1) * ((M : ℤ) + 1 - 1) = 0 by ring]
  norm_num

/-- The profile is nonnegative on its positive half-cube. -/
theorem case2_quadratic_value_nonneg (M : ℕ) {z : ℤ}
    (hz : 1 ≤ z) (hzM : z ≤ (M : ℤ)) :
    0 ≤ case2QuadraticValue M z := by
  unfold case2QuadraticValue onePoly
  apply Int.ediv_nonneg
  · have hfactor :
        (M : ℤ) * ((M : ℤ) + 1) - z * (z - 1) =
          ((M : ℤ) - z + 1) * ((M : ℤ) + z) := by ring
    rw [hfactor]
    positivity
  · norm_num

/-- At the dissipating face, the quadratic barrier has height exactly `M`. -/
theorem case2_quadratic_value_at_face (M : ℕ) :
    case2QuadraticValue M (M : ℤ) = (M : ℤ) := by
  unfold case2QuadraticValue
  have hpoly : onePoly M (M : ℤ) = 2 * (M : ℤ) := by
    dsimp [onePoly]
    ring
  have hmul := onePoly_two_mul_ediv (M := M) (x := (M : ℤ))
  rw [hpoly] at hmul
  rw [hpoly]
  nlinarith

/-- The folded quadratic profile, lifted along coordinate `k` and cut off
outside the physical even cube. -/
def case2QuadraticBarrier (d M : ℕ) (k : Fin d) (x : Site d) : ℤ :=
  if inCube d (2 * M) x then oneProfile M (oneSite (x k)) else 0

/-- The cut-off barrier is nonnegative everywhere. -/
private theorem case2_barrier_nonneg (d M : ℕ) (k : Fin d) (x : Site d) :
    0 ≤ case2QuadraticBarrier d M k x := by
  by_cases hx : inCube d (2 * M) x
  · simp [case2QuadraticBarrier, hx, oneProfile_nonneg]
  · simp [case2QuadraticBarrier, hx]

/-- On the physical cube, the cut-off barrier equals the one dimensional profile. -/
private theorem case2_barrier_eq_profile (d M : ℕ) (k : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2QuadraticBarrier d M k x = oneProfile M (oneSite (x k)) := by
  simp [case2QuadraticBarrier, hx]

/-- The positive axial neighbor agrees with the reflected one dimensional profile. -/
private theorem case2_barrier_add_axis (d M : ℕ) (k : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2QuadraticBarrier d M k (x + unit k) =
      oneProfile M (oneSite (x k + 1)) := by
  by_cases hplus : inCube d (2 * M) (x + unit k)
  · simp only [case2QuadraticBarrier, if_pos hplus]
    rw [add_unit_self]
  · have hprofile : ¬ inCube 1 (2 * M) (oneSite (x k + 1)) := by
      intro h
      apply hplus
      intro i
      by_cases hik : i = k
      · subst i
        have hi := h 0
        rw [loCoord_two_mul, hiCoord_two_mul] at hi
        rw [loCoord_two_mul, hiCoord_two_mul, add_unit_self]
        simpa [oneSite] using hi
      · rw [add_unit_other d x k i hik]
        exact hx i
    simp [case2QuadraticBarrier, hplus, oneProfile, hprofile]

/-- The negative axial neighbor agrees with the reflected one dimensional profile. -/
private theorem case2_barrier_sub_axis (d M : ℕ) (k : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2QuadraticBarrier d M k (x - unit k) =
      oneProfile M (oneSite (x k - 1)) := by
  by_cases hminus : inCube d (2 * M) (x - unit k)
  · simp only [case2QuadraticBarrier, if_pos hminus]
    rw [sub_unit_self]
  · have hprofile : ¬ inCube 1 (2 * M) (oneSite (x k - 1)) := by
      intro h
      apply hminus
      intro i
      by_cases hik : i = k
      · subst i
        have hi := h 0
        rw [loCoord_two_mul, hiCoord_two_mul] at hi
        rw [loCoord_two_mul, hiCoord_two_mul, sub_unit_self]
        simpa [oneSite] using hi
      · rw [sub_unit_other d x k i hik]
        exact hx i
    simp [case2QuadraticBarrier, hminus, oneProfile, hprofile]

/-- A positive transverse occurrence is bounded by the center barrier value. -/
private theorem case2_barrier_transverse_add_le (d M : ℕ) (k i : Fin d)
    (x : Site d) (hx : inCube d (2 * M) x) (hik : i ≠ k) :
    case2QuadraticBarrier d M k (x + unit i) ≤
      case2QuadraticBarrier d M k x := by
  by_cases hneighbor : inCube d (2 * M) (x + unit i)
  · rw [case2_barrier_eq_profile d M k _ hneighbor,
      case2_barrier_eq_profile d M k x hx]
    rw [add_unit_other d x i k (Ne.symm hik)]
  · rw [case2QuadraticBarrier, if_neg hneighbor,
      case2_barrier_eq_profile d M k x hx]
    exact oneProfile_nonneg M (oneSite (x k))

/-- A negative transverse occurrence is bounded by the center barrier value. -/
private theorem case2_barrier_transverse_sub_le (d M : ℕ) (k i : Fin d)
    (x : Site d) (hx : inCube d (2 * M) x) (hik : i ≠ k) :
    case2QuadraticBarrier d M k (x - unit i) ≤
      case2QuadraticBarrier d M k x := by
  by_cases hneighbor : inCube d (2 * M) (x - unit i)
  · rw [case2_barrier_eq_profile d M k _ hneighbor,
      case2_barrier_eq_profile d M k x hx]
    rw [sub_unit_other d x i k (Ne.symm hik)]
  · rw [case2QuadraticBarrier, if_neg hneighbor,
      case2_barrier_eq_profile d M k x hx]
    exact oneProfile_nonneg M (oneSite (x k))

/-- The selected axial pair contributes the exact one dimensional Laplacian `-1`. -/
private theorem case2_barrier_axis_sum (d M : ℕ) (k : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2QuadraticBarrier d M k (x + unit k) +
        case2QuadraticBarrier d M k (x - unit k) =
      2 * case2QuadraticBarrier d M k x - 1 := by
  have hy : inCube 1 (2 * M) (oneSite (x k)) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hx k
  have hlap := oneProfile_lap M (oneSite (x k)) hy
  simp only [lap, nbrSum, Fin.sum_univ_one] at hlap
  rw [oneSite_add, oneSite_sub] at hlap
  norm_num at hlap
  rw [case2_barrier_add_axis d M k x hx,
    case2_barrier_sub_axis d M k x hx,
    case2_barrier_eq_profile d M k x hx]
  linarith

/-- One directed-neighbor pair contributes at most twice the center value,
with the selected axis reducing it by one. -/
private theorem case2_barrier_pair_le (d M : ℕ) (k i : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2QuadraticBarrier d M k (x + unit i) +
        case2QuadraticBarrier d M k (x - unit i) ≤
      2 * case2QuadraticBarrier d M k x - (if i = k then 1 else 0) := by
  by_cases hik : i = k
  · subst i
    rw [if_pos rfl]
    exact le_of_eq (case2_barrier_axis_sum d M k x hx)
  · rw [if_neg hik]
    have hp := case2_barrier_transverse_add_le d M k i x hx hik
    have hm := case2_barrier_transverse_sub_le d M k i x hx hik
    linarith

/-- Counting each of the `2d` directed occurrences gives a strict supersolution. -/
private theorem case2_barrier_nbr_sum_le (d M : ℕ) (k : Fin d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    nbrSum (case2QuadraticBarrier d M k) x ≤
      2 * (d : ℤ) * case2QuadraticBarrier d M k x - 1 := by
  unfold nbrSum
  calc
    (∑ i : Fin d,
        (case2QuadraticBarrier d M k (x + unit i) +
          case2QuadraticBarrier d M k (x - unit i)))
        ≤ ∑ i : Fin d,
            (2 * case2QuadraticBarrier d M k x - (if i = k then 1 else 0)) := by
          exact Finset.sum_le_sum fun i _ => case2_barrier_pair_le d M k i x hx
    _ = 2 * (d : ℤ) * case2QuadraticBarrier d M k x - 1 := by
      rw [Finset.sum_sub_distrib]
      have hconst :
          (∑ _i : Fin d, (2 : ℤ) * case2QuadraticBarrier d M k x) =
            2 * (d : ℤ) * case2QuadraticBarrier d M k x := by
        simp [Finset.sum_const, Finset.card_univ]
        ring
      have hcount : (∑ i : Fin d, (if i = k then (1 : ℤ) else 0)) = 1 := by
        simp
      rw [hconst, hcount]

/-- Induction through the exact floor update bounds every odometer value by the
cut-off quadratic barrier. -/
private theorem case2_quadratic_barrier_comparison (d M : ℕ) (hd : 1 ≤ d)
    (k : Fin d) :
    ∀ t x, odoUnif d (2 * M) t x ≤ case2QuadraticBarrier d M k x := by
  intro t
  induction t with
  | zero =>
      intro x
      have hnonneg := case2_barrier_nonneg d M k x
      simp [odoUnif, odo]
      exact hnonneg
  | succ t ih =>
      intro x
      by_cases hx : inCube d (2 * M) x
      · have hupdate := case2_floor_update d M t hd x hx
        rw [hupdate]
        have hsum :
            nbrSum (odoUnif d (2 * M) t) x ≤
              nbrSum (case2QuadraticBarrier d M k) x :=
          nbrSum_mono (fun y => ih y) x
        have hK : 0 < 2 * (d : ℤ) := by
          have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
          omega
        have hbar := case2_barrier_nbr_sum_le d M k x hx
        have hnum :
            2 * (d : ℤ) + nbrSum (odoUnif d (2 * M) t) x <
              2 * (d : ℤ) * (case2QuadraticBarrier d M k x + 1) := by
          calc
            _ ≤ 2 * (d : ℤ) + nbrSum (case2QuadraticBarrier d M k) x :=
              by linarith [hsum]
            _ ≤ 2 * (d : ℤ) +
                (2 * (d : ℤ) * case2QuadraticBarrier d M k x - 1) :=
              by linarith [hbar]
            _ < 2 * (d : ℤ) *
                (case2QuadraticBarrier d M k x + 1) := by
              nlinarith
        have hnum' :
            2 * (d : ℤ) + nbrSum (odoUnif d (2 * M) t) x <
              (case2QuadraticBarrier d M k x + 1) * (2 * (d : ℤ)) := by
          nlinarith [hnum]
        have hquot := (Int.ediv_lt_iff_lt_mul hK).2 hnum'
        omega
      · have hout : odoUnif d (2 * M) (t + 1) x = 0 := by
          simpa [odoUnif] using
            odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) x hx
        rw [hout]
        simp [case2QuadraticBarrier, hx]

/-- The actual simultaneous odometer is bounded by the folded quadratic
profile at every site of the physical even cube and at every time. -/
theorem case2_odo_le_quadratic (d M t : ℕ) (hd : 1 ≤ d) (_hM : 1 ≤ M)
    (k : Fin d) (x : Site d) (hx : inCube d (2 * M) x) :
    odoUnif d (2 * M) t x ≤ case2QuadraticValue M (oneFold (x k)) := by
  have h := case2_quadratic_barrier_comparison d M hd k t x
  rw [case2_barrier_eq_profile d M k x hx] at h
  have hy : inCube 1 (2 * M) (oneSite (x k)) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hx k
  have hformula :
      oneProfile M (oneSite (x k)) =
        case2QuadraticValue M (oneFold (x k)) := by
    simp [oneProfile, case2QuadraticValue, hy, oneSite]
  rw [hformula] at h
  exact h

/-- When the selected coordinate is on the positive side of the reflection plane,
the actual odometer is bounded by `U_M(x_k)`. -/
theorem case2_odo_le_quadratic_positive (d M t : ℕ) (hd : 1 ≤ d)
    (hM : 1 ≤ M) (k : Fin d) (x : Site d) (hx : inCube d (2 * M) x)
    (hxk : 1 ≤ x k) :
    odoUnif d (2 * M) t x ≤ case2QuadraticValue M (x k) := by
  have h := case2_odo_le_quadratic d M t hd hM k x hx
  simpa [oneFold, hxk] using h

/-- At a site on a coordinate face, the quadratic barrier gives the bound `M`. -/
theorem case2_odo_le_M_at_face (d M t : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (k : Fin d) (x : Site d) (hx : inCube d (2 * M) x)
    (hxk : x k = (M : ℤ)) :
    odoUnif d (2 * M) t x ≤ (M : ℤ) := by
  have h := case2_odo_le_quadratic d M t hd hM k x hx
  have hM' : 1 ≤ (M : ℤ) := by exact_mod_cast hM
  have hfold : oneFold (x k) = (M : ℤ) := by
    simp [oneFold, hxk, hM']
  rw [hfold, case2_quadratic_value_at_face] at h
  exact h

example : odoUnif 1 2 1 (oneSite 1) = 1 := by
  have hx : inCube 1 2 (oneSite 1) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num [loCoord, hiCoord, sideHalf, oneSite]
  exact odoUnif_one 1 2 (by omega) (oneSite 1) hx

example : odoUnif 1 4 2 (oneSite 1) = 2 := by
  have hx : inCube 1 4 (oneSite 1) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num [loCoord, hiCoord, sideHalf, oneSite]
  rw [odoUnif_two 1 2 (by omega) (by omega) (oneSite 1) hx]
  have hall : ∀ i : Fin 1,
      inCube 1 4 (oneSite 1 + unit i) ∧ inCube 1 4 (oneSite 1 - unit i) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    constructor <;> intro j
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      norm_num [inCube, loCoord, hiCoord, sideHalf, oneSite, unit]
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      norm_num [inCube, loCoord, hiCoord, sideHalf, oneSite, unit]
  simp [hall]

example : odoUnif 2 6 2 (fun _ => 2) = 2 := by
  have hx : inCube 2 6 (fun _ : Fin 2 => 2) := by
    intro i
    norm_num [loCoord, hiCoord, sideHalf]
  rw [odoUnif_two 2 3 (by omega) (by omega) (fun _ => 2) hx]
  have hall : ∀ i : Fin 2,
      inCube 2 6 ((fun _ => 2) + unit i) ∧
        inCube 2 6 ((fun _ => 2) - unit i) := by
    intro i
    constructor <;> intro j
    · rw [add_unit_apply]
      by_cases hji : j = i <;> simp [hji] <;>
        norm_num [loCoord, hiCoord, sideHalf]
    · rw [sub_unit_apply]
      by_cases hji : j = i <;> simp [hji] <;>
        norm_num [loCoord, hiCoord, sideHalf]
  simp [hall]

end DimRed
