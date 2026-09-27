/-
Case 1 of the strong derivative clause, `dimred.tex:1322-1332`: below the topple
time `τ_M` the two-step difference `v_t(x) - v_t(x + 2 e_k)` is at most `2 x_k`
at every point of the positive orthant, for every direction `k`.

The paper runs Lemma 2.4 (the difference comparison) on the sorted domain with
the family of shifts `2 e_k` and the weights `g_k(x) = 2 x_k`.  Working on the
positive orthant instead removes the rotating boundary from the statement: the
neighbours of a point of `P_M` are again in `P_M`, or are the reflection of the
point itself (a coordinate equal to one), or lie off the cube (a coordinate
equal to `M`).  The three cases are the three terms of the floor step, and the
reflecting case at a coordinate equal to one is where weak facet compatibility
enters, exactly as in the paper's one-dimensional argument.

The bound is used at the centre point `1_d`, which is the `i = 0` branch of the
frozen clause; the branch `i ≥ 1` is `strong_deriv_pos_head`.
-/
import DimRed.Support.StrongDerivRaw
import DimRed.Support.CornerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The floor step of the early-time two-step difference: the neighbour sums at
time `n` are bounded term by term, so the difference at time `n + 1` obeys the
same bound.  The family at time `n` is used at every neighbour of the positive
orthant, and the two neighbours outside it are the reflected one (a coordinate
equal to one) and the dissipating one (a coordinate equal to `M`). -/
theorem two_diff_floor_step (d M n : ℕ) (hd : 1 ≤ d) (k : Fin d) (x : Site d)
    (hx : inPos d M x) (hkM : x k + 2 ≤ (M : ℤ))
    (ih : ∀ (k : Fin d) (x : Site d), inPos d M x →
      odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k + unit k) ≤ 2 * x k)
    (hrefl : x k = 1 → odoUnif d (2 * M) n x ≤ odoUnif d (2 * M) n (x + unit k)) :
    odoUnif d (2 * M) (n + 1) x - odoUnif d (2 * M) (n + 1) (x + unit k + unit k)
      ≤ 2 * x k := by
  have hx' : inCube d (2 * M) x := inPos_inCube hx
  have hxw : inCube d (2 * M) (x + (unit k + unit k)) := by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul]
    have h := hx i
    simp only [Pi.add_apply, unit, Pi.single_apply]
    by_cases hik : i = k
    · subst hik
      simp only [if_true]
      omega
    · simp only [if_neg hik, add_zero]
      omega
  have hG : nbrSum (fun y : Site d => 2 * y k) x = 2 * (d : ℤ) * (2 * x k) := by
    have h := nbrSum_affine (fun m : Fin d => if m = k then (2:ℤ) else 0) 0 x
    have h1 : (fun y : Site d => ∑ m : Fin d, (if m = k then (2:ℤ) else 0) * y m + 0)
        = fun y => 2 * y k := by
      funext y
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [hb]
      · intro hb; exact absurd (Finset.mem_univ k) hb
    have h3 : (∑ m : Fin d, (if m = k then (2:ℤ) else 0) * x m + 0) = 2 * x k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [hb]
      · intro hb; exact absurd (Finset.mem_univ k) hb
    rw [h1, h3] at h
    exact h
  have hfloor := floor_step d M hd n n x (unit k + unit k) hx' hxw (2 * x k) ?_
  · have hcomm : x + unit k + unit k = x + (unit k + unit k) := by abel
    rw [hcomm]
    simpa [Nat.add_assoc] using hfloor
  · refine nbrSum_sub_le_of_terms (odoUnif d (2 * M) n) (odoUnif d (2 * M) n)
      x (unit k + unit k) (fun y => 2 * y k) hG ?_ ?_
    · intro m
      rcases inPos_add_unit_or hx m with h | h
      · have hc : x + unit m + (unit k + unit k) = (x + unit m) + unit k + unit k := by abel
        rw [hc]
        exact ih k (x + unit m) h
      · have hterm := term_outside d M n n (x + unit m) (unit k + unit k)
          (not_inCube_add_unit_of_eq m h)
        have h1 : 0 ≤ (x + unit m) k := by
          rw [add_unit_apply]
          have := (hx k).1
          split_ifs <;> omega
        linarith [hterm]
    · intro m
      rcases inPos_sub_unit_or hx m with h | h
      · have hc : x - unit m + (unit k + unit k) = (x - unit m) + unit k + unit k := by abel
        rw [hc]
        exact ih k (x - unit m) h
      · by_cases hmk : m = k
        · subst hmk
          have hc : x - unit m + (unit m + unit m) = x - unit m + unit m + unit m := by abel
          rw [hc, term_reflect_pure d M n n x m h]
          have hg0 : (2 * (x - unit m) m : ℤ) = 0 := by rw [sub_unit_self, h]; ring
          rw [hg0]
          linarith [hrefl h]
        · have hwl : (unit k + unit k : Site d) m = 0 := by
            simp only [Pi.add_apply, unit_apply_ne hmk, add_zero]
          have hterm := term_reflect d M n n x (unit k + unit k) m h hwl
          have hvk : (x - unit m) k = x k := sub_unit_other d x m k (Ne.symm hmk)
          rw [hterm, hvk]
          have hc : x + (unit k + unit k) = x + unit k + unit k := by abel
          rw [hc]
          exact ih k x hx

/-- Case 1 of the strong derivative clause: below the topple time the two-step
difference is at most `2 x_k` at every point of the positive orthant.  The
statement is proved for every time up to `T`, and weak facet compatibility is
consumed only at times strictly below `T`, which is what the joint induction
supplies. -/
theorem odo_two_diff_early (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s) :
    ∀ t, t ≤ T → (t : ℕ∞) < toppleTime d M → ∀ (k : Fin d) (x : Site d),
      inPos d M x →
      odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k + unit k)
        ≤ 2 * x k := by
  intro t
  induction t with
  | zero =>
    intro _ _ k x hx
    have h1 : odoUnif d (2 * M) 0 x = 0 := rfl
    have h2 : odoUnif d (2 * M) 0 (x + unit k + unit k) = 0 := rfl
    rw [h1, h2]
    have hk := (hx k).1
    omega
  | succ n ih =>
    intro hs ht k x hx
    have ih' : ∀ (k : Fin d) (x : Site d), inPos d M x →
        odoUnif d (2 * M) n x - odoUnif d (2 * M) n (x + unit k + unit k) ≤ 2 * x k :=
      fun k x hx => ih (by omega)
        (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) (le_of_lt ht)) k x hx
    by_cases htop : x k + 2 ≤ (M : ℤ)
    · by_cases hk1 : x k = 1
      · by_cases htopple : odoUnif d (2 * M) n x = odoUnif d (2 * M) n (x + unit k) + 1
        · have hn1 : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with h0 | h
            · subst h0
              simp only [odoUnif, odo] at htopple
              omega
            · exact h
          have hstay := weak_raw d M n hn1 (hW n hn1 (by omega)) x hx k hk1 htopple
          have hfar : odoUnif d (2 * M) n (x + unit k + unit k)
              ≤ odoUnif d (2 * M) (n + 1) (x + unit k + unit k) :=
            odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (Nat.le_succ n) (x + unit k + unit k)
          have hih' := ih' k x hx
          linarith
        · have hrefl : x k = 1 → odoUnif d (2 * M) n x ≤ odoUnif d (2 * M) n (x + unit k) := by
            intro _
            by_contra hc
            push Not at hc
            have hle := odo_first_diff d M hd hM n k x (by rw [hk1])
            omega
          exact two_diff_floor_step d M n hd k x hx htop ih' hrefl
      · exact two_diff_floor_step d M n hd k x hx htop ih' (fun h => absurd h hk1)
    · push Not at htop
      have hkM : (M : ℤ) - 1 ≤ x k := by omega
      have hout : ¬ inCube d (2 * M) (x + unit k + unit k) := by
        intro hc
        have h := hc k
        rw [hiCoord_two_mul] at h
        have hk' : (x + unit k + unit k) k = x k + 1 + 1 := by
          rw [add_unit_apply, add_unit_apply]
          simp
        rw [hk'] at h
        omega
      have hzero : odoUnif d (2 * M) (n + 1) (x + unit k + unit k) = 0 :=
        odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (n + 1) _ hout
      rw [hzero, sub_zero]
      by_cases hkM' : x k = (M : ℤ)
      · have hle : odoUnif d (2 * M) (n + 1) x ≤ (M : ℤ) := by
          have h1 : odoUnif d (2 * M) (n + 1) x
              ≤ odoUnif d (2 * M) (n + 1) (cornerPoint d M) := by
            simpa only [odoUnif] using odo_le_corner d M hd (2 * (d : ℤ))
              (by positivity) (by omega) (n + 1) x (inPos_inCube hx) k hkM'
          have h2 := odo_corner_le_M d M hd hM (n + 1)
          linarith
        have h2 : 2 * x k = 2 * (M : ℤ) := by rw [hkM']
        linarith
      · have hxk : x k = (M : ℤ) - 1 := by
          have h1 := (hx k).2
          omega
        have hM2 : (1 : ℤ) ≤ (M : ℤ) - 1 := by
          have h1 := (hx k).1
          omega
        have hfirst := odo_first_diff d M hd hM (n + 1) k x (by rw [hxk]; exact hM2)
        have hinner : odoUnif d (2 * M) (n + 1) (x + unit k) ≤ (M : ℤ) - 1 := by
          have h2 : odoUnif d (2 * M) (n + 1) (cornerPoint d M) ≤ (M : ℤ) - 1 :=
            odo_corner_le_of_lt_toppleTime d M hd hM (n + 1) ht
          have h3 : odoUnif d (2 * M) (n + 1) (x + unit k)
              ≤ odoUnif d (2 * M) (n + 1) (cornerPoint d M) := by
            simpa only [odoUnif] using odo_le_corner d M hd (2 * (d : ℤ))
              (by positivity) (by omega) (n + 1) (x + unit k) (by
                intro i
                rw [loCoord_two_mul, hiCoord_two_mul]
                have h := hx i
                simp only [Pi.add_apply, unit, Pi.single_apply]
                by_cases hik : i = k
                · subst hik
                  simp only [if_true]
                  omega
                · simp only [if_neg hik, add_zero]
                  omega) k (by rw [add_unit_self, hxk]; ring)
          linarith
        have h2 : 2 * x k = 2 * ((M : ℤ) - 1) := by rw [hxk]
        linarith

/-- The `i = 0` branch of the frozen strong derivative clause: at the centre
point `1_d`, below the topple time, the two-step difference is at most two. -/
theorem strong_deriv_zero_head (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < t → RegWeak d M s)
    (ht : (t : ℕ∞) < toppleTime d M) :
    odoUnif d (2 * M) t (fun _ : Fin d => (1 : ℤ))
      - odoUnif d (2 * M) t (fun i : Fin d => if i = ⟨0, by omega⟩ then 3 else 1) ≤ 2 := by
  have hpos : inPos d M (fun _ : Fin d => (1 : ℤ)) := by
    intro l
    constructor
    · norm_num
    · have h1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (by omega : 1 ≤ M)
      exact h1
  have h := odo_two_diff_early d M t hd (by omega) hW t le_rfl ht ⟨0, by omega⟩
    (fun _ : Fin d => (1 : ℤ)) hpos
  have h2 : (fun _ : Fin d => (1 : ℤ)) + unit ⟨0, by omega⟩ + unit ⟨0, by omega⟩
      = fun i : Fin d => if i = ⟨0, by omega⟩ then 3 else 1 := by
    funext i
    simp only [Pi.add_apply, unit, Pi.single_apply]
    by_cases hi : i = ⟨0, by omega⟩
    · subst hi
      norm_num
    · rw [if_neg hi, if_neg hi]
      norm_num
  rw [h2] at h
  norm_num at h
  linarith

end DimRed
