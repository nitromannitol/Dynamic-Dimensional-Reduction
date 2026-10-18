import DimRed.Support.Case2FirstDifference
import DimRed.Support.AxisStep
import DimRed.Support.StrongDerivPure

/-!
# Auxiliary steps for the all-time facet induction

The quadratic barrier closes the dissipating-face case of the time-shifted
estimate. The first-difference estimate closes its no-fire case, and previous
facet compatibility closes the facet lag step. Coordinate permutation
symmetry closes the rotating boundary case of the pure second difference.
These lemmas do not assume current-time dimensional reduction or a sorted
comparison.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- At a dissipating face, the quadratic barrier and zero padding prove the
time-shifted estimate `A_t`. -/
theorem case2_odo_time_shifted_difference_face (d M t : ℕ) (hd : 1 ≤ d)
    (hM : 2 ≤ M) (_ht : 1 ≤ t) (k : Fin d) (x : Site d)
    (hx : case2Pos d M x) (hxk : x k = (M : ℤ)) :
    odoUnif d (2 * M) t x - odoUnif d (2 * M) (t - 1) (x + unit k) ≤ x k := by
  have hxCube : inCube d (2 * M) x := by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul]
    have hi := hx i
    omega
  have hout : ¬ inCube d (2 * M) (x + unit k) := by
    intro hc
    have hi := (hc k).2
    rw [hiCoord_two_mul, add_unit_self] at hi
    omega
  have hzero : odoUnif d (2 * M) (t - 1) (x + unit k) = 0 := by
    exact odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1)
      (x + unit k) hout
  have hface := case2_odo_le_M_at_face d M t hd (by omega) k x hxCube hxk
  rw [hzero]
  linarith

/-- If the raised site stays during the last update, the first-difference
estimate gives the corresponding case of `A_t`. -/
theorem case2_odo_time_shifted_difference_of_stay (d M t : ℕ) (hd : 1 ≤ d)
    (hM : 2 ≤ M) (_ht : 1 ≤ t) (k : Fin d) (x : Site d)
    (hx : case2Pos d M x)
    (hstay : odoUnif d (2 * M) t (x + unit k) =
      odoUnif d (2 * M) (t - 1) (x + unit k)) :
    odoUnif d (2 * M) t x - odoUnif d (2 * M) (t - 1) (x + unit k) ≤ x k := by
  have hM' : 1 ≤ M := by omega
  have hfirst := case2_odo_first_difference d M t hd hM' k x hx
  rw [← hstay]
  exact hfirst.2

/-- The facet lag estimate follows from the first difference when its previous
gap is zero, and from the previous compatibility conclusion when that gap is
one. -/
theorem case2_odo_facet_lag_of_previous_compatibility (d M t : ℕ)
    (hd : 1 ≤ d) (hM : 2 ≤ M) (ht : 1 ≤ t) (k : Fin d) (x : Site d)
    (hx : case2Pos d M x) (hxk : x k = 1)
    (hcompat : odoUnif d (2 * M) (t - 1) x =
        odoUnif d (2 * M) (t - 1) (x + unit k) + 1 →
      odoUnif d (2 * M) t x = odoUnif d (2 * M) (t - 1) x ∧
        odoUnif d (2 * M) t (x + unit k) =
          odoUnif d (2 * M) (t - 1) (x + unit k) + 1) :
    odoUnif d (2 * M) t (x + unit k) ≥ odoUnif d (2 * M) (t - 1) x := by
  have hM' : 1 ≤ M := by omega
  have hprev := case2_odo_first_difference d M (t - 1) hd hM' k x hx
  have hprevlo : 0 ≤ odoUnif d (2 * M) (t - 1) x -
      odoUnif d (2 * M) (t - 1) (x + unit k) := by
    simpa only [hxk] using hprev.1
  have hprevhi : odoUnif d (2 * M) (t - 1) x -
      odoUnif d (2 * M) (t - 1) (x + unit k) ≤ 1 := by
    simpa only [hxk] using hprev.2
  by_cases hgap : odoUnif d (2 * M) (t - 1) x =
      odoUnif d (2 * M) (t - 1) (x + unit k) + 1
  · have hstep := hcompat hgap
    rw [hstep.2, hgap]
  · have hEq : odoUnif d (2 * M) (t - 1) x =
      odoUnif d (2 * M) (t - 1) (x + unit k) := by omega
    have hmono := odo_mono d (2 * M) (fun _ => 2 * (d : ℤ))
      (show t - 1 ≤ t by omega) (x + unit k)
    have hmono' : odoUnif d (2 * M) (t - 1) (x + unit k) ≤
        odoUnif d (2 * M) t (x + unit k) := by
      simpa only [odoUnif] using hmono
    rw [hEq]
    exact hmono'

/-- If a mixed second-difference bound is available and a larger coordinate
is exactly one above `x k`, permutation symmetry converts it to the pure
second-difference bound at that rotating boundary point. -/
theorem case2_rotating_pure_difference (d M t : ℕ) (k l : Fin d)
    (hkl : k ≠ l) (x : Site d) (hrotate : x l = x k + 1)
    (hB : odoUnif d (2 * M) t x -
        odoUnif d (2 * M) t (x + unit k + unit l) ≤ x k + x l - 1) :
    odoUnif d (2 * M) t x -
        odoUnif d (2 * M) t (x + unit k + unit k) ≤ 2 * x k := by
  have hbase : (x + unit k) k = (x + unit k) l := by
    calc
      (x + unit k) k = x k + 1 := add_unit_self d x k
      _ = x l := by rw [hrotate]
      _ = (x + unit k) l := by
        rw [add_unit_other d x k l (Ne.symm hkl)]
  have hswap := odo_swap_add d M (2 * (d : ℤ)) t (x + unit k) k l hkl hbase
  have hmirror : odoUnif d (2 * M) t (x + unit k + unit k) =
      odoUnif d (2 * M) t (x + unit k + unit l) := by
    simpa only [odoUnif] using hswap
  calc
    odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k + unit k)
        = odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k + unit l) := by
            rw [hmirror]
    _ ≤ x k + x l - 1 := hB
    _ = 2 * x k := by rw [hrotate]; omega

private theorem case2_pos_in_cube {d M : ℕ} {x : Site d}
    (hx : case2Pos d M x) : inCube d (2 * M) x := by
  intro i
  rw [loCoord_two_mul, hiCoord_two_mul]
  have hi := hx i
  omega

private theorem case2_positive_neighbor_head_add {d : ℕ} (k l i : Fin d)
    (hkl : k ≠ l) (x : Site d) (hhead : x k + 2 ≤ x l) :
    (x + unit i) k < (x + unit i) l := by
  by_cases hik : i = k
  · subst i
    rw [add_unit_self, add_unit_other d x k l (Ne.symm hkl)]
    omega
  · by_cases hil : i = l
    · subst i
      rw [add_unit_other d x l k hkl, add_unit_self]
      omega
    · rw [add_unit_other d x i k (Ne.symm hik),
        add_unit_other d x i l (Ne.symm hil)]
      omega

private theorem case2_positive_neighbor_head_sub {d : ℕ} (k l i : Fin d)
    (hkl : k ≠ l) (x : Site d) (hhead : x k + 2 ≤ x l) :
    (x - unit i) k < (x - unit i) l := by
  by_cases hik : i = k
  · subst i
    rw [sub_unit_self, sub_unit_other d x k l (Ne.symm hkl)]
    omega
  · by_cases hil : i = l
    · subst i
      rw [sub_unit_other d x l k hkl, sub_unit_self]
      omega
    · rw [sub_unit_other d x i k (Ne.symm hik),
        sub_unit_other d x i l (Ne.symm hil)]
      omega

private theorem case2_pos_add_of_below_top {d M : ℕ} {x : Site d}
    (hx : case2Pos d M x) (i : Fin d) (hi : x i < (M : ℤ)) :
    case2Pos d M (x + unit i) := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [add_unit_self]
    have h := hx i
    omega
  · rw [add_unit_other d x i j hji]
    exact hx j

private theorem case2_pos_sub_of_above_bottom {d M : ℕ} {x : Site d}
    (hx : case2Pos d M x) (i : Fin d) (hi : x i > 1) :
    case2Pos d M (x - unit i) := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [sub_unit_self]
    have h := hx i
    omega
  · rw [sub_unit_other d x i j hji]
    exact hx j

private theorem case2_double_step_pos {d M : ℕ} {k l : Fin d} {x : Site d}
    (hx : case2Pos d M x) (hhead : x k + 2 ≤ x l) :
    case2Pos d M (x + unit k + unit k) := by
  intro i
  have hcoord : (x + unit k + unit k) i = x i + (if i = k then 2 else 0) := by
    by_cases hik : i = k
    · subst i
      rw [add_unit_self, add_unit_self]
      omega
    · rw [add_unit_other d (x + unit k) k i hik,
        add_unit_other d x k i hik]
      simp [hik]
  rw [hcoord]
  by_cases hik : i = k
  · subst i
    have hk := hx k
    have hl := (hx l).2
    omega
  · simpa [hik] using hx i

private theorem case2_pure_difference_gap_two_step_terms (d M n : ℕ)
    (hd : 1 ≤ d) (_hM : 2 ≤ M) (k l : Fin d) (hkl : k ≠ l)
    (x : Site d) (hx : case2Pos d M x) (hhead : x k + 2 ≤ x l)
    (hreflect_zero : x k = 1 →
      odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k) = 0)
    (hprev : ∀ y : Site d, case2Pos d M y → y k < y l →
      odoUnif d (2 * M) n y -
        odoUnif d (2 * M) n (y + (unit k + unit k)) ≤ 2 * y k) :
    odoUnif d (2 * M) (n + 1) x -
      odoUnif d (2 * M) (n + 1) (x + (unit k + unit k)) ≤ 2 * x k := by
  let w : Site d := unit k + unit k
  have hxCube := case2_pos_in_cube hx
  have hfarPos := case2_double_step_pos hx hhead
  have hfarCube := case2_pos_in_cube hfarPos
  have hG : nbrSum (fun y : Site d => 2 * y k) x =
      2 * (d : ℤ) * (2 * x k) := by
    have ha := nbrSum_affine (fun i : Fin d => if i = k then (2 : ℤ) else 0) 0 x
    have hfun :
        (fun y : Site d => ∑ i : Fin d, (if i = k then (2 : ℤ) else 0) * y i + 0) =
          fun y => 2 * y k := by
      funext y
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        simp [hik]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    have hval :
        (∑ i : Fin d, (if i = k then (2 : ℤ) else 0) * x i + 0) = 2 * x k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        simp [hik]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    rw [hfun, hval] at ha
    exact ha
  have hsum : nbrSum (odoUnif d (2 * M) n) x -
      nbrSum (odoUnif d (2 * M) n) (x + w) ≤ 2 * (d : ℤ) * (2 * x k) := by
    refine nbrSum_sub_le_of_terms (odoUnif d (2 * M) n) (odoUnif d (2 * M) n)
      x w (fun y => 2 * y k) hG ?_ ?_
    · intro i
      by_cases htop : x i = (M : ℤ)
      · have hout : ¬ inCube d (2 * M) (x + unit i) := by
          intro hc
          have hi := (hc i).2
          rw [hiCoord_two_mul, add_unit_self] at hi
          omega
        have hterm := term_outside d M n n (x + unit i) w hout
        have hypos : 0 ≤ (x + unit i) k := by
          rw [add_unit_apply]
          have hk := (hx k).1
          split_ifs <;> omega
        have hweight : 0 ≤ 2 * (x + unit i) k := by omega
        linarith
      · have hy : case2Pos d M (x + unit i) :=
          case2_pos_add_of_below_top hx i (by have hi := (hx i).2; omega)
        have hhead' := case2_positive_neighbor_head_add k l i hkl x hhead
        exact hprev (x + unit i) hy hhead'
    · intro i
      by_cases hbottom : x i = 1
      · by_cases hik : i = k
        · subst i
          have hreflect : odoUnif d (2 * M) n (x - unit k) =
              odoUnif d (2 * M) n x := by
            have h := odo_sub_unit_of_one d M (2 * (d : ℤ)) n x k hbottom
            simpa only [odoUnif] using h
          have hshift : x - unit k + w = x + unit k := by
            funext j
            by_cases hjk : j = k
            · subst j
              simp [w, unit]
              ring
            · simp [w, unit, hjk]
          have hweight : 2 * (x - unit k) k = 0 := by
            rw [sub_unit_self, hbottom]
            norm_num
          rw [hreflect, hshift, hreflect_zero hbottom, hweight]
        · have hw : w i = 0 := by
            simp [w, unit, hik]
          have hterm := term_reflect d M n n x w i hbottom hw
          have hweight : 2 * (x - unit i) k = 2 * x k := by
            rw [sub_unit_other d x i k (Ne.symm hik)]
          rw [hterm, hweight]
          exact hprev x hx (by omega)
      · have hy : case2Pos d M (x - unit i) :=
          case2_pos_sub_of_above_bottom hx i (by have hi := (hx i).1; omega)
        have hhead' := case2_positive_neighbor_head_sub k l i hkl x hhead
        exact hprev (x - unit i) hy hhead'
  have hcoord : x + w = x + unit k + unit k := by
    funext i
    exact (add_assoc (x i) (unit k i) (unit k i)).symm
  have hfarCube' : inCube d (2 * M) (x + w) := by
    rw [hcoord]
    exact hfarCube
  have hfloor := floor_step d M hd n n x w hxCube hfarCube' (2 * x k) hsum
  rw [hcoord] at hfloor
  simpa only [add_assoc] using hfloor

/-- In the nonrotating interior of the comparison region, the exact floor
update advances `C_t` from the previous-time estimate. The only exceptional
reflected occurrence is the selected coordinate at one; previous no-fire
compatibility closes that term. -/
theorem case2_odo_pure_difference_gap_two_step (d M n : ℕ) (hd : 1 ≤ d)
    (hM : 2 ≤ M) (k l : Fin d) (hkl : k ≠ l) (x : Site d)
    (hx : case2Pos d M x) (hhead : x k + 2 ≤ x l)
    (hcompat : odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k) = 1 →
      odoUnif d (2 * M) (n + 1) x = odoUnif d (2 * M) n x)
    (hprev : ∀ y : Site d, case2Pos d M y → y k < y l →
      odoUnif d (2 * M) n y -
        odoUnif d (2 * M) n (y + (unit k + unit k)) ≤ 2 * y k) :
    odoUnif d (2 * M) (n + 1) x -
      odoUnif d (2 * M) (n + 1) (x + unit k + unit k) ≤ 2 * x k := by
  have hM' : 1 ≤ M := by omega
  have hfirst := case2_odo_first_difference d M n hd hM' k x hx
  by_cases hk1 : x k = 1
  · have hgaplo : 0 ≤ odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k) := by
      simpa only [hk1] using hfirst.1
    have hgaphi : odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k) ≤ 1 := by
      simpa only [hk1] using hfirst.2
    by_cases hgap : odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k) = 1
    · have hstay := hcompat hgap
      have hprevious := hprev x hx (by omega)
      have hmono := odo_mono d (2 * M) (fun _ => 2 * (d : ℤ))
        (Nat.le_succ n) (x + (unit k + unit k))
      have hmono' : odoUnif d (2 * M) n (x + (unit k + unit k)) ≤
          odoUnif d (2 * M) (n + 1) (x + (unit k + unit k)) := by
        simpa only [odoUnif] using hmono
      have hnow : odoUnif d (2 * M) (n + 1) x -
          odoUnif d (2 * M) (n + 1) (x + (unit k + unit k)) ≤
            odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + (unit k + unit k)) := by
        rw [hstay]
        linarith
      have hresult := le_trans hnow hprevious
      simpa only [show x + (unit k + unit k) = x + unit k + unit k by abel] using hresult
    · have hzero : odoUnif d (2 * M) n x -
          odoUnif d (2 * M) n (x + unit k) = 0 := by omega
      have hresult := case2_pure_difference_gap_two_step_terms d M n hd hM k l hkl
        x hx hhead (fun _ => hzero) hprev
      simpa only [show x + (unit k + unit k) = x + unit k + unit k by abel] using hresult
  · have hresult := case2_pure_difference_gap_two_step_terms d M n hd hM k l hkl
      x hx hhead (fun h => (hk1 h).elim) hprev
    simpa only [show x + (unit k + unit k) = x + unit k + unit k by abel] using hresult

/-- The all-time pure second-difference estimate holds at side length two
whenever some other positive coordinate is larger. The endpoint is outside
the cube, and the quadratic barrier bounds the first point by two. -/
theorem case2_odo_pure_difference_side_two (d t : ℕ) (hd : 1 ≤ d)
    (k : Fin d) (x : Site d) (hx : case2Pos d 2 x)
    (hhead : ∃ l : Fin d, x k < x l) :
    odoUnif d 4 t x - odoUnif d 4 t (x + unit k + unit k) ≤ 2 * x k := by
  obtain ⟨l, hl⟩ := hhead
  have hxk : x k = 1 := by
    have hk := hx k
    have hlhi := (hx l).2
    omega
  have hxl : x l = 2 := by
    have hllo := (hx l).1
    have hlhi := (hx l).2
    rw [hxk] at hl
    omega
  have hxCube : inCube d 4 x := by
    intro i
    change (1 - (2 : ℤ)) ≤ x i ∧ x i ≤ (2 : ℤ)
    have hi := hx i
    omega
  have hout : ¬ inCube d 4 (x + unit k + unit k) := by
    intro hc
    have hi := hc k
    change (1 - (2 : ℤ)) ≤ (x + unit k + unit k) k ∧
      (x + unit k + unit k) k ≤ (2 : ℤ) at hi
    have hcoord : (x + unit k + unit k) k = x k + 2 := by
      calc
        (x + unit k + unit k) k = (x + unit k) k + 1 := add_unit_self d _ k
        _ = (x k + 1) + 1 := by rw [add_unit_self]
        _ = x k + 2 := by ring
    rw [hcoord, hxk] at hi
    omega
  have hzero : odoUnif d 4 t (x + unit k + unit k) = 0 := by
    exact odo_eq_zero_outside d 4 (fun _ => 2 * (d : ℤ)) t _ hout
  have hface := case2_odo_le_M_at_face d 2 t hd (by omega) l x hxCube hxl
  change odoUnif d 4 t x ≤ (2 : ℤ) at hface
  rw [hzero, hxk]
  linarith

example :
    ∃ x : Site 2, ∃ k : Fin 2,
      (∀ i : Fin 2, 1 ≤ x i ∧ x i ≤ (2 : ℤ)) ∧
        x k < x 0 ∧
        odoUnif 2 4 3 x - odoUnif 2 4 3 (x + unit k + unit k) = 2 * x k := by
  let x : Site 2 := fun i => if i = 0 then 2 else 1
  let k : Fin 2 := 1
  refine ⟨x, k, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · norm_num [x, k]
  · have hx : inCube 2 4 x := by
      intro i
      fin_cases i <;> norm_num [inCube, loCoord, hiCoord, sideHalf, x]
    have hy : inCube 2 4 x := hx
    let j : Fin 2 := Fin.succ 0
    have hminus0 : odoUnif 2 4 2 (x - unit (0 : Fin 2)) = 2 := by
      have hsite : inCube 2 4 (x - unit (0 : Fin 2)) := by
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x]
      have hall : ∀ i : Fin 2,
          inCube 2 4 (x - unit (0 : Fin 2) + unit i) ∧
            inCube 2 4 (x - unit (0 : Fin 2) - unit i) := by
        intro i
        fin_cases i <;>
          norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x]
      rw [odoUnif_two 2 2 (by omega) (by omega) _ hsite]
      simp [hall]
    have hplus1 : odoUnif 2 4 2 (x + unit j) = 1 := by
      have hsite : inCube 2 4 (x + unit j) := by
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x, j]
      have hnall : ¬ ∀ i : Fin 2,
          inCube 2 4 (x + unit j + unit i) ∧
            inCube 2 4 (x + unit j - unit i) := by
        intro hall
        have hi := (hall 0).1
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x, j] at hi
      rw [odoUnif_two 2 2 (by omega) (by omega) _ hsite]
      simp [hnall]
    have hminus1 : odoUnif 2 4 2 (x - unit j) = 1 := by
      have hsite : inCube 2 4 (x - unit j) := by
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x, j]
      have hnall : ¬ ∀ i : Fin 2,
          inCube 2 4 (x - unit j + unit i) ∧
            inCube 2 4 (x - unit j - unit i) := by
        intro hall
        have hi := (hall 0).1
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x, j] at hi
      rw [odoUnif_two 2 2 (by omega) (by omega) _ hsite]
      simp [hnall]
    have hplus0 : odoUnif 2 4 2 (x + unit (0 : Fin 2)) = 0 := by
      have hout0 : ¬ inCube 2 4 (x + unit (0 : Fin 2)) := by
        norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x]
      exact odo_eq_zero_outside 2 4 (fun _ => 2 * (2 : ℤ)) 2 _ hout0
    have hsum : nbrSum (odoUnif 2 4 2) x = 4 := by
      unfold nbrSum
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_one]
      rw [hplus0, hminus0]
      change 0 + 2 +
        (odoUnif 2 4 2 (x + unit j) + odoUnif 2 4 2 (x - unit j)) = 4
      rw [hplus1, hminus1]
      norm_num
    have hvalue : odoUnif 2 4 3 x = 2 := by
      have hfloor := case2_floor_update 2 2 2 (by omega) x hx
      rw [hsum] at hfloor
      norm_num at hfloor
      exact hfloor
    have hout : ¬ inCube 2 4 (x + unit k + unit k) := by
      intro hc
      have hi := hc k
      norm_num [inCube, loCoord, hiCoord, sideHalf, unit, Pi.single_apply, x, k] at hi
    have hzero : odoUnif 2 4 3 (x + unit k + unit k) = 0 := by
      exact odo_eq_zero_outside 2 4 (fun _ => 2 * (2 : ℤ)) 3 _ hout
    rw [hvalue, hzero]
    norm_num [x, k]

end DimRed
