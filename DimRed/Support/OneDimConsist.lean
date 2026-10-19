import DimRed.Support.AxisStep
import DimRed.Support.NonnegativeUpdate

/-
The one-dimensional inductive self-similarity step in Proposition 4.1: the self-similarity
clause (`base_dimension:consistency`) of `dimred-corrected-arxiv.tex`.  The file also records the one-dimensional centre
estimates used in the exceptional `x = 2` row of the induction.
-/
namespace DimRed

open LatticeProb

theorem site_one_eq_const (x : Site 1) : x = fun _ => x 0 := by
  funext i
  rw [show i = 0 from Fin.eq_zero i]

theorem site_one_add_unit (x : ℤ) :
    (fun _ : Fin 1 => x) + unit 0 = fun _ => x + 1 := by
  funext i
  rw [show i = 0 from Fin.eq_zero i]
  simp [unit]

theorem site_one_sub_unit (x : ℤ) :
    (fun _ : Fin 1 => x) - unit 0 = fun _ => x - 1 := by
  funext i
  rw [show i = 0 from Fin.eq_zero i]
  simp [unit]

theorem inCube_one_two_mul (M : ℕ) (x : ℤ) (hx1 : 1 ≤ x) (hxM : x ≤ (M : ℤ)) :
    inCube 1 (2 * M) (fun _ => x) := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  simp only [loCoord_two_mul, hiCoord_two_mul]
  change 1 - (M : ℤ) ≤ x ∧ x ≤ (M : ℤ)
  omega

theorem inCube_one_two_mul_sub (M : ℕ) (hM : 2 ≤ M) (x : ℤ)
    (hx1 : 2 ≤ x) (hxM : x ≤ (M : ℤ)) :
    inCube 1 (2 * (M - 1)) (fun _ => x - 1) := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  simp only [loCoord_two_mul, hiCoord_two_mul]
  change 1 - (M - 1 : ℕ) ≤ x - 1 ∧ x - 1 ≤ (M - 1 : ℕ)
  omega

theorem not_inCube_one_two_mul_of_gt (M : ℕ) (x : ℤ) (hx : (M : ℤ) < x) :
    ¬ inCube 1 (2 * M) (fun _ => x) := by
  intro h
  have hi := h (0 : Fin 1)
  have hi' := hi.2
  change x ≤ hiCoord (2 * M) at hi'
  rw [hiCoord_two_mul] at hi'
  omega

theorem odo_one_center_no_topple (M s : ℕ) (hM : 1 ≤ M)
    (h : odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) =
      odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) + 1) :
    odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) =
    odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) := by
  have hx : inCube 1 (2 * M) (fun _ => (1 : ℤ)) :=
    inCube_one_two_mul M 1 (by omega) (by omega)
  have hstep := odo_succ_eq 1 (2 * M) (fun _ => (2 : ℤ)) s
    (fun _ => (1 : ℤ)) hx
  have href := odo_reflect_coord 1 M 2 s (fun _ => (0 : ℤ)) (0 : Fin 1)
  have href' : odoUnif 1 (2 * M) s (fun _ => (0 : ℤ)) =
      odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) := by
    have he : (fun k : Fin 1 => if k = 0 then 1 - (0 : ℤ) else 0) =
        fun _ => (1 : ℤ) := by
      funext k
      rw [show k = 0 from Fin.eq_zero k]
      simp
    rw [he] at href
    change odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
      odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (0 : ℤ)) at href
    exact href.symm
  change odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (0 : ℤ)) =
    odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) at href'
  change odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) (fun _ => (1 : ℤ)) =
      odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ))
  change odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
      odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) + 1 at h
  rw [sandp, lap, nbrSum, Fin.sum_univ_one, site_one_add_unit,
    site_one_sub_unit] at hstep
  norm_num at hstep
  rw [href'] at hstep
  omega

theorem odo_one_center_diff (M : ℕ) (hM : 1 ≤ M) :
    ∀ s : ℕ,
      0 ≤ odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) -
          odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) ∧
      odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) -
          odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) ≤ 1 := by
  intro s
  induction s with
  | zero => simp [odoUnif, odo]
  | succ s ih =>
      have hmono : odoUnif 1 (2 * M) (s + 1) (fun _ => (2 : ℤ)) ≤
          odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) := by
        have h := odo_axis_refl 1 M (by norm_num) 2 (by norm_num) (by norm_num) (s + 1)
          (fun _ => (1 : ℤ)) (0 : Fin 1) (by norm_num)
        rw [site_one_add_unit] at h
        simpa [odoUnif] using h
      have h1 : 0 ≤ odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) -
          odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) ∧
          odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) -
            odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) ≤ 1 := by
        simpa [odoUnif] using
          (odo_succ_sub_bounds 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)))
      have h2 : 0 ≤ odoUnif 1 (2 * M) (s + 1) (fun _ => (2 : ℤ)) -
          odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) ∧
          odoUnif 1 (2 * M) (s + 1) (fun _ => (2 : ℤ)) -
            odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) ≤ 1 := by
        simpa [odoUnif] using
          (odo_succ_sub_bounds 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)))
      have hupper : odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) -
          odoUnif 1 (2 * M) (s + 1) (fun _ => (2 : ℤ)) ≤ 1 := by
        by_cases he : odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) -
            odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) = 1
        · have hn := odo_one_center_no_topple M s hM (by omega)
          omega
        · omega
      exact ⟨by omega, hupper⟩

theorem odo_one_consist_step
    (M t : ℕ) (hM : 2 ≤ M) (ht : (t : ℕ∞) ≤ toppleTime 1 (M - 1))
    (hprev : ∀ t' : ℕ, t' < t → ∀ z : Site 1, 2 ≤ z 0 → z 0 ≤ (M : ℤ) →
      odoUnif 1 (2 * M) t' z =
        odoUnif 1 (2 * (M - 1)) t' (fun _ => z 0 - 1))
    (hfacet : ∀ s : ℕ, s + 2 = t →
      ((s + 1 : ℕ) : ℕ∞) < toppleTime 1 (M - 1) →
        odoUnif 1 (2 * (M - 1)) s (fun _ => (1 : ℤ)) =
            odoUnif 1 (2 * (M - 1)) s (fun _ => (2 : ℤ)) + 1 →
          odoUnif 1 (2 * (M - 1)) (s + 1) (fun _ => (1 : ℤ)) =
            odoUnif 1 (2 * (M - 1)) s (fun _ => (1 : ℤ)) ∧
          odoUnif 1 (2 * (M - 1)) (s + 1) (fun _ => (2 : ℤ)) =
            odoUnif 1 (2 * (M - 1)) s (fun _ => (2 : ℤ)) + 1)
    (y : Site 1) (hy2 : 2 ≤ y 0) (hyM : y 0 ≤ (M : ℤ)) :
    odoUnif 1 (2 * M) t y =
      odoUnif 1 (2 * (M - 1)) t (fun _ => y 0 - 1) := by
  have hy : y = fun _ => y 0 := site_one_eq_const y
  rw [hy]
  change odo 1 (2 * M) (fun _ => (2 : ℤ)) t (fun _ => y 0) =
    odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) t (fun _ => y 0 - 1)
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp [odo]
  · by_cases ht1 : t = 1
    · subst t
      have hbig := inCube_one_two_mul M (y 0) (by omega) hyM
      have hsmall := inCube_one_two_mul_sub M hM (y 0) hy2 hyM
      simp [odo, hbig, hsmall, lap, nbrSum]
    · have ht2 : 2 ≤ t := by omega
      set s : ℕ := t - 1 with hs
      set r : ℕ := t - 2 with hr
      have hst : s + 1 = t := by omega
      have hrt : r + 2 = t := by omega
      have hrs : r + 1 = s := by omega
      have hslt : s < t := by omega
      have hrlt : r < t := by omega
      have hbig : inCube 1 (2 * M) (fun _ => y 0) :=
        inCube_one_two_mul M (y 0) (by omega) hyM
      have hsmall : inCube 1 (2 * (M - 1)) (fun _ => y 0 - 1) :=
        inCube_one_two_mul_sub M hM (y 0) hy2 hyM
      have hptbig := DimRed.bounded_point_update 1 (2 * M) (by omega) (fun _ => (2 : ℤ))
        (fun _ _ => by omega) (fun _ _ => by omega) s (fun _ => y 0) hbig
      have hptsmall := DimRed.bounded_point_update 1 (2 * (M - 1)) (by omega) (fun _ => (2 : ℤ))
        (fun _ _ => by omega) (fun _ _ => by omega) s
        (fun _ => y 0 - 1) hsmall
      rw [hst] at hptbig hptsmall
      by_cases hy3 : 3 ≤ y 0
      · have hminus := hprev s hslt (fun _ => y 0 - 1) (by omega) (by omega)
        have hplus :
            odoUnif 1 (2 * M) s ((fun _ => y 0) + unit 0) =
              odoUnif 1 (2 * (M - 1)) s ((fun _ => y 0 - 1) + unit 0) := by
          by_cases hylt : y 0 < (M : ℤ)
          · have h := hprev s hslt (fun _ => y 0 + 1) (by omega) (by omega)
            simpa [site_one_add_unit] using h
          · have houtbig : ¬ inCube 1 (2 * M) ((fun _ => y 0) + unit 0) := by
              have : (M : ℤ) < y 0 + 1 := by omega
              simpa [site_one_add_unit] using
                not_inCube_one_two_mul_of_gt M (y 0 + 1) this
            have houtsmall : ¬ inCube 1 (2 * (M - 1))
                ((fun _ => y 0 - 1) + unit 0) := by
              have : ((M - 1 : ℕ) : ℤ) < y 0 := by omega
              simpa [site_one_add_unit] using
                not_inCube_one_two_mul_of_gt (M - 1) (y 0) this
            have hzeroBig : odoUnif 1 (2 * M) s ((fun _ => y 0) + unit 0) = 0 := by
              simpa [odoUnif] using
                odo_eq_zero_outside 1 (2 * M) (fun _ => (2 : ℤ)) s _ houtbig
            have hzeroSmall : odoUnif 1 (2 * (M - 1)) s
                ((fun _ => y 0 - 1) + unit 0) = 0 := by
              simpa [odoUnif] using
                odo_eq_zero_outside 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s _ houtsmall
            rw [hzeroBig, hzeroSmall]
        have hminus' :
            odoUnif 1 (2 * M) s ((fun _ => y 0) - unit 0) =
              odoUnif 1 (2 * (M - 1)) s ((fun _ => y 0 - 1) - unit 0) := by
          have h := hprev s hslt (fun _ => y 0 - 1) (by omega) (by omega)
          simpa [site_one_sub_unit] using h
        have hplusRaw :
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => y 0 + 1) =
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s
                (fun _ => y 0 - 1 + 1) := by
          simpa [odoUnif, site_one_add_unit] using hplus
        have hminusRaw :
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => y 0 - 1) =
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s
                (fun _ => y 0 - 1 - 1) := by
          simpa [odoUnif, site_one_sub_unit] using hminus'
        rw [hptbig, hptsmall]
        simp only [nbrSum, Fin.sum_univ_one, site_one_add_unit, site_one_sub_unit]
        rw [hplusRaw, hminusRaw]
      · have hy2eq : y 0 = 2 := by omega
        rw [hy2eq] at hptbig hptsmall ⊢
        have htwoU := hprev s hslt (fun _ => (2 : ℤ)) (by omega) (by omega)
        have htwo :
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) =
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) := by
          simpa [odoUnif] using htwoU
        have hthree :
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) =
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) := by
          by_cases hM3 : 3 ≤ M
          · simpa [odoUnif] using
              hprev s hslt (fun _ => (3 : ℤ)) (by omega) (by omega)
          · have houtbig : ¬ inCube 1 (2 * M) (fun _ => (3 : ℤ)) := by
              exact not_inCube_one_two_mul_of_gt M 3 (by omega)
            have houtsmall : ¬ inCube 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) := by
              exact not_inCube_one_two_mul_of_gt (M - 1) 2 (by omega)
            have hzeroBig :=
              odo_eq_zero_outside 1 (2 * M) (fun _ => (2 : ℤ)) s _ houtbig
            have hzeroSmall :=
              odo_eq_zero_outside 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s _ houtsmall
            rw [hzeroBig, hzeroSmall]
        have hzero :
            odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (0 : ℤ)) =
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) := by
          have h := odo_reflect_coord 1 (M - 1) 2 s (fun _ => (0 : ℤ)) (0 : Fin 1)
          have he : (fun k : Fin 1 => if k = 0 then 1 - (0 : ℤ) else 0) =
              fun _ => (1 : ℤ) := by
            funext k
            rw [show k = 0 from Fin.eq_zero k]
            simp
          rw [he] at h
          exact h.symm
        have hcenterBigU := odo_one_center_diff M (by omega) s
        have hcenterSmallU := odo_one_center_diff (M - 1) (by omega) s
        have hcenterBig :
            0 ≤ odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) -
                odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) ∧
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) -
                odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) ≤ 1 := by
          simpa [odoUnif] using hcenterBigU
        have hcenterSmall :
            0 ≤ odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) -
                odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) ∧
            odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) -
                odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) ≤ 1 := by
          simpa [odoUnif] using hcenterSmallU
        have hbigpt := hptbig
        have hsmallpt := hptsmall
        simp only [nbrSum, Fin.sum_univ_one, site_one_add_unit, site_one_sub_unit] at hbigpt hsmallpt
        norm_num at hbigpt hsmallpt
        rw [hzero] at hsmallpt
        rw [← htwo, ← hthree] at hsmallpt
        have htime' : ((r + 1 : ℕ) : ℕ∞) < toppleTime 1 (M - 1) := by
          have hltNat : r + 1 < t := by omega
          have hltInf : (r + 1 : ℕ∞) < (t : ℕ∞) := by exact_mod_cast hltNat
          exact lt_of_lt_of_le hltInf ht
        by_cases hAB :
            odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
              odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ))
        · rw [hAB] at hbigpt
          exact hbigpt.trans hsmallpt.symm
        · have hAB' :
              odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
                odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) + 1 := by
            have hmono := hcenterBig.1
            omega
          by_cases hBC :
              odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
                odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ))
          · have hBCbig :
                odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) =
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) := by
              calc
                _ = odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) := htwo
                _ = odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) := hBC
                _ = _ := hthree.symm
            rw [hAB', hBCbig] at hbigpt
            rw [hBCbig] at hsmallpt
            have hfloor :
                (2 + (odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) +
                    (odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) + 1))) / 2 =
                  (2 + (odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) +
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)))) / 2 := by
              omega
            exact hbigpt.trans (hfloor.trans hsmallpt.symm)
          · have hBC' :
                odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (1 : ℤ)) =
                  odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) + 1 := by
              have hmono := hcenterSmall.1
              omega
            have hfacet' := hfacet r hrt htime'
            have hsmallr := hprev r hrlt (fun _ => (2 : ℤ)) (by omega) (by omega)
            have hsmallr2 :
                odoUnif 1 (2 * (M - 1)) r (fun _ => (2 : ℤ)) =
                  odoUnif 1 (2 * M) r (fun _ => (3 : ℤ)) := by
              symm
              by_cases hM3 : 3 ≤ M
              · exact hprev r hrlt (fun _ => (3 : ℤ)) (by omega) (by omega)
              · have houtbig : ¬ inCube 1 (2 * M) (fun _ => (3 : ℤ)) := by
                  exact not_inCube_one_two_mul_of_gt M 3 (by omega)
                have houtsmall : ¬ inCube 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) := by
                  exact not_inCube_one_two_mul_of_gt (M - 1) 2 (by omega)
                have hzeroBig : odoUnif 1 (2 * M) r (fun _ => (3 : ℤ)) = 0 := by
                  simpa [odoUnif] using
                    odo_eq_zero_outside 1 (2 * M) (fun _ => (2 : ℤ)) r _ houtbig
                have hzeroSmall : odoUnif 1 (2 * (M - 1)) r (fun _ => (2 : ℤ)) = 0 := by
                  simpa [odoUnif] using
                    odo_eq_zero_outside 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r _ houtsmall
                rw [hzeroBig, hzeroSmall]
            have hsmallr_diff_raw :
                odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) =
                  odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) + 1 := by
              have hcenterR :
                  0 ≤ odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) -
                      odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) ∧
                  odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) -
                      odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) ≤ 1 := by
                simpa [odoUnif] using odo_one_center_diff (M - 1) (by omega) r
              have hcenterR' :
                  0 ≤ odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) -
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) ∧
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) -
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) ≤ 1 := by
                simpa [odoUnif] using odo_one_center_diff M (by omega) r
              have hsmallrRaw :
                  odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) =
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) := by
                simpa [odoUnif] using hsmallr.symm
              have hsmallr2Raw :
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (3 : ℤ)) =
                    odo 1 (2 * (M - 1)) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) := by
                simpa [odoUnif] using hsmallr2.symm
              have hBinc := odo_succ_sub_bounds 1 (2 * M) (fun _ => (2 : ℤ)) r
                (fun _ => (2 : ℤ))
              have hCinc := odo_succ_sub_bounds 1 (2 * M) (fun _ => (2 : ℤ)) r
                (fun _ => (3 : ℤ))
              have hAinc := odo_succ_sub_bounds 1 (2 * M) (fun _ => (2 : ℤ)) r
                (fun _ => (1 : ℤ))
              have hAlow := hAinc.1
              have hAupper := hAinc.2
              have hBlow := hBinc.1
              have hBupper := hBinc.2
              have hClow := hCinc.1
              have hCupper := hCinc.2
              have hRsmalllow := hcenterR.1
              have hRsmallupper := hcenterR.2
              have hRbiglow := hcenterR'.1
              have hRbigupper := hcenterR'.2
              have hBCs :
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (2 : ℤ)) =
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) s (fun _ => (3 : ℤ)) + 1 := by
                have h := hBC'
                rw [← htwo, ← hthree] at h
                exact h
              rw [← hrs] at hBCs
              have hABr := hAB'
              rw [← hrs] at hABr
              have hBClow :
                  0 ≤ odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) -
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (3 : ℤ)) := by
                omega
              have hBCupper :
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) -
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (3 : ℤ)) ≤ 1 := by
                omega
              by_cases hBCzero :
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) =
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (3 : ℤ))
              · have hA0 :
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) =
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (2 : ℤ)) + 1 := by
                  have hA0bound := hcenterR'.2
                  have hA0nonneg := hcenterR'.1
                  omega
                have hnotopU := odo_one_center_no_topple M r (by omega) (by
                  simpa [odoUnif] using hA0)
                have hnotop :
                    odo 1 (2 * M) (fun _ => (2 : ℤ)) (r + 1) (fun _ => (1 : ℤ)) =
                      odo 1 (2 * M) (fun _ => (2 : ℤ)) r (fun _ => (1 : ℤ)) := by
                  simpa [odoUnif] using hnotopU
                omega
              · omega
            have hsmallr_diff :
                odoUnif 1 (2 * (M - 1)) r (fun _ => (1 : ℤ)) =
                  odoUnif 1 (2 * (M - 1)) r (fun _ => (2 : ℤ)) + 1 := by
              simpa [odoUnif] using hsmallr_diff_raw
            have hfacet'' := hfacet' hsmallr_diff
            have hBCu :
                odoUnif 1 (2 * (M - 1)) s (fun _ => (1 : ℤ)) =
                  odoUnif 1 (2 * (M - 1)) s (fun _ => (2 : ℤ)) + 1 := by
              simpa [odoUnif] using hBC'
            rw [hrs] at hfacet''
            rcases hfacet'' with ⟨hstay, htop⟩
            omega

end DimRed
