import DimRed.Support.DifferenceStep
import DimRed.Support.NonnegativeUpdate
/-
The finite-time strong derivative estimate in dimension one, using the
two-step comparison function from `dimred.tex:1012-1029`.
-/
import DimRed.Support.DerivBound
import DimRed.Frozen.Prelim.DifferenceComparison

namespace DimRed

open LatticeProb

/- A time-bounded form of the first-derivative estimate is needed because the
corner bound used here is available only before the relevant topple time. -/
theorem odo_deriv_bound_until (d M : ℕ) (c : ℤ)
    (k T : ℕ) (hd : 1 ≤ d) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) (hk : 1 ≤ k)
    (hcor : ∀ s, s ≤ T →
      odo d (2 * M) (fun _ => c) s (cornerPoint d M) ≤ (k : ℤ) * (M : ℤ)) :
    ∀ t, t ≤ T → ∀ j : Fin d, ∀ x : Site d, 1 ≤ x j →
      odo d (2 * M) (fun _ => c) t x
        - odo d (2 * M) (fun _ => c) t (x + unit j) ≤ (k : ℤ) * x j := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  intro t
  induction t with
  | zero =>
    intro _ j x hxj
    have h : (0 : ℤ) ≤ (k : ℤ) * x j := mul_nonneg (by omega) (by omega)
    simpa [odo] using h
  | succ n ih =>
    intro ht j x hxj
    by_cases hx : inCube d (2 * M) x
    · by_cases hxa : inCube d (2 * M) (x + unit j)
      · rcases lt_or_eq_of_le (ih (by omega) j x hxj) with hlt | heq
        · have h1 := (odo_succ_sub_bounds d (2 * M) (fun _ => c) n x).2
          have h2 := (odo_succ_sub_bounds d (2 * M) (fun _ => c) n (x + unit j)).1
          omega
        · have hkey : ∀ i : Fin d,
              (odo d (2 * M) (fun _ => c) n (x + unit i)
                 - odo d (2 * M) (fun _ => c) n (x + unit j + unit i))
              + (odo d (2 * M) (fun _ => c) n (x - unit i)
                 - odo d (2 * M) (fun _ => c) n (x + unit j - unit i))
              ≤ 2 * ((k : ℤ) * x j) := by
            intro i
            have e1 : x + unit j + unit i = (x + unit i) + unit j := by abel
            have e2 : x + unit j - unit i = (x - unit i) + unit j := by abel
            rw [e1, e2]
            by_cases hij : i = j
            · have hv1 : (x + unit i) j = x j + 1 := by rw [hij, add_unit_self]
              have t1 := ih (by omega) j (x + unit i) (by rw [hv1]; omega)
              rw [hv1] at t1
              by_cases hx2 : 2 ≤ x j
              · have hv2 : (x - unit i) j = x j - 1 := by rw [hij, sub_unit_self]
                have t2 := ih (by omega) j (x - unit i) (by rw [hv2]; omega)
                rw [hv2] at t2
                nlinarith [t1, t2]
              · have hx1 : x j = 1 := by omega
                have he : odo d (2 * M) (fun _ => c) n (x - unit i)
                    = odo d (2 * M) (fun _ => c) n x := by
                  rw [hij]
                  exact odo_sub_unit_of_one d M c n x j hx1
                have he2 : (x - unit i) + unit j = x := by rw [hij]; abel
                rw [he, he2, hx1]
                rw [hx1] at t1
                nlinarith [t1]
            · have hji : j ≠ i := fun h => hij h.symm
              have hv1 : (x + unit i) j = x j := add_unit_other d x i j hji
              have hv2 : (x - unit i) j = x j := sub_unit_other d x i j hji
              have t1 := ih (by omega) j (x + unit i) (by rw [hv1]; omega)
              have t2 := ih (by omega) j (x - unit i) (by rw [hv2]; omega)
              rw [hv1] at t1
              rw [hv2] at t2
              linarith
          have hsplit : nbrSum (odo d (2 * M) (fun _ => c) n) x
              - nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)
              = ∑ i : Fin d, ((odo d (2 * M) (fun _ => c) n (x + unit i)
                  - odo d (2 * M) (fun _ => c) n (x + unit j + unit i))
                + (odo d (2 * M) (fun _ => c) n (x - unit i)
                  - odo d (2 * M) (fun _ => c) n (x + unit j - unit i))) := by
            simp only [nbrSum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
          have hAB : nbrSum (odo d (2 * M) (fun _ => c) n) x
              - nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)
              ≤ 2 * (d : ℤ) * ((k : ℤ) * x j) := by
            rw [hsplit]
            refine le_trans (Finset.sum_le_sum (fun i _ => hkey i)) ?_
            simp [Finset.sum_const, Finset.card_univ]
            ring_nf
            exact le_rfl
          rw [DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ hx,
            DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ hxa]
          have h1 : (c + nbrSum (odo d (2 * M) (fun _ => c) n) x) / (2 * (d : ℤ))
              ≤ (c + nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)
                  + 2 * (d : ℤ) * ((k : ℤ) * x j)) / (2 * (d : ℤ)) := by
            exact Int.ediv_le_ediv hdpos (by linarith [hAB])
          have h2 : (c + nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)
                  + 2 * (d : ℤ) * ((k : ℤ) * x j)) / (2 * (d : ℤ))
              = (c + nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j))
                / (2 * (d : ℤ)) + (k : ℤ) * x j := by
            exact Int.add_mul_ediv_left _ _ (ne_of_gt hdpos)
          rw [h2] at h1
          linarith
      · have hxjM : x j = (M : ℤ) := by
          by_contra hcon
          refine hxa fun l => ?_
          rw [loCoord_two_mul, hiCoord_two_mul]
          by_cases hl : l = j
          · rw [hl, add_unit_self]
            have h := hx j
            rw [loCoord_two_mul, hiCoord_two_mul] at h
            omega
          · rw [add_unit_other d x j l hl]
            have h := hx l
            rw [loCoord_two_mul, hiCoord_two_mul] at h
            omega
        rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hxa,
          hxjM, sub_zero]
        exact le_trans
          (odo_le_corner d M hd c hc0 hc1 (n + 1) x hx j hxjM)
          (hcor (n + 1) (by omega))
    · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hx]
      have h1 := odo_nonneg d (2 * M) (fun _ => c) (n + 1) (x + unit j)
      have h2 : (0 : ℤ) ≤ (k : ℤ) * x j := mul_nonneg (by omega) (by omega)
      omega

theorem odo_one_strong_deriv (M t : ℕ) (hM : 2 ≤ M)
    (ht : (t : ℕ∞) < toppleTime 1 M)
    (hcorner : ∀ s : ℕ, (s : ℕ∞) < toppleTime 1 M →
      odoUnif 1 (2 * M) s (fun _ => (M : ℤ)) ≤ (M : ℤ) - 1)
    (hweak : ∀ s : ℕ, (s : ℕ∞) < toppleTime 1 M →
      odoUnif 1 (2 * M) s (fun _ => (1 : ℤ))
          - odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) = 1 →
      odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ))
          - odoUnif 1 (2 * M) (s + 1) (fun _ => (3 : ℤ)) ≤ 2)
    (y : Site 1) (hy1 : 1 ≤ y 0) (hyM : y 0 ≤ (M : ℤ)) :
      odoUnif 1 (2 * M) t y
        - odoUnif 1 (2 * M) t (y + unit 0 + unit 0) ≤ 2 * y 0 := by
  let e : Site 1 := unit 0
  let w : Site 1 := e + e
  let g : Site 1 → ℤ := fun x => 2 * x 0
  let zero : Site 1 := fun _ => 0
  let one : Site 1 := fun _ => 1
  let two : Site 1 := fun _ => 2
  let three : Site 1 := fun _ => 3
  let four : Site 1 := fun _ => 4
  have hpoint : ∀ (a : ℤ),
      (fun _ : Fin 1 => a) + e = (fun _ => a + 1) ∧
      (fun _ : Fin 1 => a) - e = (fun _ => a - 1) := by
    intro a
    constructor <;> funext i
    · have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      simp [e, unit]
    · have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      simp [e, unit]
  have hpoint_w : ∀ (a : ℤ),
      (fun _ : Fin 1 => a) + w = (fun _ => a + 2) := by
    intro a
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    simp [w, e, unit]
  have hcornerPoint : cornerPoint 1 M = fun _ => (M : ℤ) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    simp [cornerPoint]
  have simplex_one : ∀ z : Site 1, 1 ≤ z 0 → z 0 ≤ (M : ℤ) → inSimplex 1 M z := by
    intro z hz1 hzM
    refine ⟨?_, ?_⟩
    · intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      exact ⟨hz1, hzM⟩
    · intro i j _
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      have hj : j = (0 : Fin 1) := Fin.eq_zero j
      subst hi
      subst hj
      exact le_rfl
  have hyS : inSimplex 1 M y := simplex_one y hy1 hyM
  have hg : SuperharmonicIn 1 M g := by
    intro x _hx _hnb
    simp only [g, nbrSum, Fin.sum_univ_one]
    rw [add_unit_self, sub_unit_self]
    ring_nf
    exact le_rfl
  have hderiv : ∀ s, s ≤ t → ∀ x : Site 1, 1 ≤ x 0 →
      odoUnif 1 (2 * M) s x - odoUnif 1 (2 * M) s (x + e) ≤ x 0 := by
    intro s hs x hx
    have hcor' : ∀ r, r ≤ s →
        odo 1 (2 * M) (fun _ => (2 : ℤ)) r (cornerPoint 1 M)
          ≤ (1 : ℤ) * (M : ℤ) := by
      intro r hrs
      have hrs' : (r : ℕ∞) < toppleTime 1 M := by
        exact lt_of_le_of_lt (by exact_mod_cast (Nat.le_trans hrs hs)) ht
      rw [hcornerPoint]
      have hc := hcorner r hrs'
      have hle : (M : ℤ) - 1 ≤ (M : ℤ) := by omega
      simpa [odoUnif] using le_trans hc hle
    have hbound := odo_deriv_bound_until 1 M 2 1 s (by omega) (by omega)
      (by omega) (by omega) hcor'
    have h := hbound s (by omega) (0 : Fin 1) x hx
    simpa [odoUnif, e] using h
  have hmain : ∀ s, s ≤ t → ∀ x : Site 1, inSimplex 1 M x →
      odoUnif 1 (2 * M) s x - odoUnif 1 (2 * M) s (x + w) - g x ≤ 0 := by
    intro s
    induction s with
    | zero =>
        intro _ x hx
        have hx0 := (hx.1 0).1
        simp [odoUnif, g, odo]
        omega
    | succ s ih =>
        intro hs x hx
        have hst : (s : ℕ∞) < toppleTime 1 M := by
          have hle : (s : ℕ∞) ≤ (t : ℕ∞) := by
            exact_mod_cast (Nat.le_trans (by omega) hs)
          exact lt_of_le_of_lt hle ht
        have hprev : ∀ z, inSimplex 1 M z →
            odoUnif 1 (2 * M) s z - odoUnif 1 (2 * M) s (z + w) - g z ≤ 0 :=
          fun z hz => ih (by omega) z hz
        by_cases hb : bdry M 0 x ∨ bdry M w x
        · have hbdry :
              (inCube 1 (2 * M) (x + w) ∧
                nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) x
                  - nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) (x + w)
                  - 2 * (1 : ℤ) * g x ≤ 0) ∨
              (odoUnif 1 (2 * M) (s + 1) x
                - odoUnif 1 (2 * M) (s + 1) (x + w) - g x ≤ 0) := by
            by_cases hxcube : inCube 1 (2 * M) (x + w)
            · by_cases hxone : x 0 = 1
              · have hone : one + e = two := by simpa [one, two, e] using (hpoint 1).1
                have hDupper := hderiv s (by omega) one (by simp [one])
                have hDlower :
                    0 ≤ odoUnif 1 (2 * M) s one - odoUnif 1 (2 * M) s two := by
                  have haxis := odo_axis_refl 1 M (by omega) (2 : ℤ) (by omega)
                    (by omega) s one (0 : Fin 1) (by simp [one])
                  rw [hone] at haxis
                  simpa [odoUnif] using haxis
                have hDupper' : odoUnif 1 (2 * M) s one
                    - odoUnif 1 (2 * M) s two ≤ 1 := by
                  rw [← hone]
                  simpa [one] using hDupper
                by_cases hdiff : odoUnif 1 (2 * M) s one
                    - odoUnif 1 (2 * M) s two = 1
                · right
                  have hw := hweak s hst hdiff
                  have hone : one + w = three := by simpa [one, three, w, e] using hpoint_w 1
                  have ex : x = one := by
                    funext i
                    have hi : i = (0 : Fin 1) := Fin.eq_zero i
                    subst hi
                    simpa [one] using hxone
                  rw [ex]
                  simpa [one, three, w, g, hone] using hw
                · left
                  refine ⟨hxcube, ?_⟩
                  have hzero : odoUnif 1 (2 * M) s one
                      - odoUnif 1 (2 * M) s two = 0 := by omega
                  have htwo := hprev two (simplex_one two (by simp [two]) (by simp [two]; omega))
                  have href := odo_reflect_coord 1 M 2 s zero (0 : Fin 1)
                  have href_eq : (fun k => if k = (0 : Fin 1) then
                      1 - zero 0 else zero k) = one := by
                    funext i
                    have hi : i = (0 : Fin 1) := Fin.eq_zero i
                    subst hi
                    simp [zero, one]
                  have hzero_two : two + w = four := by
                    simpa [two, four, w, e] using hpoint_w 2
                  rw [href_eq] at href
                  have hsum : nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) one
                      - nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) (one + w) ≤ 4 := by
                    simp only [nbrSum, Fin.sum_univ_one]
                    have hone : one + e = two := by simpa [one, two, e] using (hpoint 1).1
                    have hminus : one - e = zero := by simpa [one, zero, e] using (hpoint 1).2
                    have honew : one + w = three := by simpa [one, three, w, e] using hpoint_w 1
                    have hthree_plus : three + e = four := by simpa [three, four, e] using (hpoint 3).1
                    have hthree_minus : three - e = two := by simpa [three, two, e] using (hpoint 3).2
                    rw [hone, hminus, honew, hthree_plus, hthree_minus]
                    have htwo' : odoUnif 1 (2 * M) s two
                        - odoUnif 1 (2 * M) s four ≤ 4 := by
                      simpa [g, two, four, hzero_two] using htwo
                    have h01 : odoUnif 1 (2 * M) s one = odoUnif 1 (2 * M) s two := by omega
                    have href' : odoUnif 1 (2 * M) s zero = odoUnif 1 (2 * M) s one := by
                      simpa [odoUnif] using href.symm
                    simp only [odoUnif] at htwo' h01 href'
                    norm_num at htwo' h01 href'
                    linarith
                  have ex : x = one := by
                    funext i
                    have hi : i = (0 : Fin 1) := Fin.eq_zero i
                    subst hi
                    simpa [one] using hxone
                  rw [ex]
                  simpa [g, one] using (show
                    nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) one
                      - nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) (one + w)
                      - 2 * (1 : ℤ) * g one ≤ 0 by linarith [hsum])
              · left
                refine ⟨hxcube, ?_⟩
                have hxgt : 1 < x 0 := lt_of_le_of_ne (hx.1 0).1 (Ne.symm hxone)
                have hxone' : 2 ≤ x 0 := by omega
                have hxm : inSimplex 1 M (x - e) := by
                  apply simplex_one
                  · change 1 ≤ x 0 - 1
                    omega
                  · change x 0 - 1 ≤ (M : ℤ)
                    have hxupper := (hx.1 0).2
                    omega
                have hxp : inSimplex 1 M (x + e) := by
                  apply simplex_one
                  · rw [add_unit_self]
                    omega
                  · rw [add_unit_self]
                    have hc := hxcube 0
                    rw [loCoord_two_mul, hiCoord_two_mul] at hc
                    have hc' : x 0 + 2 ≤ (M : ℤ) := by
                      simpa [w, e, unit] using hc.2
                    omega
                have hleft := hprev (x - e) hxm
                have hright := hprev (x + e) hxp
                have hleft' : odoUnif 1 (2 * M) s (x - e)
                    - odoUnif 1 (2 * M) s (x + e) - g (x - e) ≤ 0 := by
                  have heq : x - e + w = x + e := by
                    dsimp [w, e]
                    abel
                  rw [heq] at hleft
                  exact hleft
                have hright' : odoUnif 1 (2 * M) s (x + e)
                    - odoUnif 1 (2 * M) s (x + w + e) - g (x + e) ≤ 0 := by
                  have heq : x + e + w = x + w + e := by abel
                  rw [heq] at hright
                  exact hright
                have hsum : nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) x
                    - nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) (x + w) ≤ 4 * x 0 := by
                  simp only [nbrSum, Fin.sum_univ_one]
                  have heq : x + w - e = x + e := by
                    dsimp [w, e]
                    abel
                  rw [heq]
                  simp only [e]
                  simp only [e] at hleft' hright'
                  simp only [odoUnif] at hleft' hright'
                  simp [g] at hleft' hright'
                  linarith [hleft', hright']
                simpa [g] using (show
                  nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) x
                    - nbrSum (odo 1 (2 * M) (fun _ => (2 : ℤ)) s) (x + w)
                    - 2 * (1 : ℤ) * g x ≤ 0 by linarith [hsum])
            · right
              have hxlarge : (M : ℤ) < x 0 + 2 := by
                by_contra hnot
                apply hxcube
                intro i
                have hi : i = (0 : Fin 1) := Fin.eq_zero i
                subst hi
                have hwcoord : (x + w) 0 = x 0 + 2 := by
                  simp [w, e, unit]
                have hnot' : x 0 + 2 ≤ (M : ℤ) := le_of_not_gt hnot
                have hc' : 1 - (M : ℤ) ≤ x 0 + 2 ∧ x 0 + 2 ≤ (M : ℤ) :=
                  ⟨by
                    have hxlower := (hx.1 0).1
                    have hM0 : (0 : ℤ) ≤ (M : ℤ) := by omega
                    omega, hnot'⟩
                simpa [loCoord_two_mul, hiCoord_two_mul, hwcoord] using hc'
              have hxval : x 0 = (M : ℤ) ∨ x 0 = (M : ℤ) - 1 := by
                have hxupper := (hx.1 0).2
                omega
              rcases hxval with hxM | hxM1
              · have ex : x = cornerPoint 1 M := by
                  funext i
                  have hi : i = (0 : Fin 1) := Fin.eq_zero i
                  subst hi
                  simp [cornerPoint, hxM]
                rw [ex]
                have hzero : ¬ inCube 1 (2 * M) (cornerPoint 1 M + w) := by
                  simpa [ex] using hxcube
                change odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) (cornerPoint 1 M)
                  - odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) (cornerPoint 1 M + w)
                  - g (cornerPoint 1 M) ≤ 0
                rw [odo_eq_zero_outside 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1)
                  (cornerPoint 1 M + w) hzero, sub_zero]
                have hc := hcorner (s + 1) (by
                  exact lt_of_le_of_lt (by exact_mod_cast hs) ht)
                have hc' : odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1)
                    (fun _ => (M : ℤ)) ≤ (M : ℤ) - 1 := by
                  simpa [odoUnif, hcornerPoint] using hc
                rw [hcornerPoint]
                simpa [g] using (show
                  odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) (fun _ => (M : ℤ))
                      ≤ 2 * (M : ℤ) by linarith [hc'])
              · let xm : Site 1 := fun _ => (M : ℤ) - 1
                have ex : x = xm := by
                  funext i
                  have hi : i = (0 : Fin 1) := Fin.eq_zero i
                  subst hi
                  exact hxM1
                rw [ex]
                have hzero : ¬ inCube 1 (2 * M) (xm + w) := by
                  simpa [ex] using hxcube
                change odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) xm
                  - odo 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1) (xm + w)
                  - g xm ≤ 0
                rw [odo_eq_zero_outside 1 (2 * M) (fun _ => (2 : ℤ)) (s + 1)
                  (xm + w) hzero, sub_zero]
                have hM' : (1 : ℤ) < (M : ℤ) := by exact_mod_cast (show 1 < M by omega)
                have hd1 := hderiv (s + 1) (by omega) xm (by simp [xm]; omega)
                have heq : xm + e = cornerPoint 1 M := by
                  funext i
                  have hi : i = (0 : Fin 1) := Fin.eq_zero i
                  subst hi
                  rw [add_unit_self]
                  simp [xm, cornerPoint]
                rw [heq] at hd1
                have hc := hcorner (s + 1) (by
                  exact lt_of_le_of_lt (by exact_mod_cast hs) ht)
                have hc' : odoUnif 1 (2 * M) (s + 1) (fun _ => (M : ℤ))
                    ≤ (M : ℤ) - 1 := by
                  simpa [hcornerPoint] using hc
                have hd1' : odoUnif 1 (2 * M) (s + 1) xm
                    - odoUnif 1 (2 * M) (s + 1) (fun _ => (M : ℤ)) ≤ (M : ℤ) - 1 := by
                  have hxm0 : xm 0 = (M : ℤ) - 1 := by simp [xm]
                  rw [hcornerPoint, hxm0] at hd1
                  exact hd1
                have hbound : odoUnif 1 (2 * M) (s + 1) xm ≤ 2 * ((M : ℤ) - 1) := by
                  linarith [hd1', hc']
                simpa [odoUnif, g, xm] using hbound
          have hstep := difference_boundary_step 1 M (by omega) (2 : ℤ)
            (by omega) (by omega) w g s x hx
          rcases hbdry with hfirst | hsecond
          · exact hstep hfirst.1 (by simpa [odoUnif] using hfirst.2)
          · exact hsecond
        · have hstrict : (∀ i : Fin 1, x i < (M : ℤ)) ∧
              (∀ i : Fin 1, 1 < x i) ∧
              (∀ i j : Fin 1, i < j → x j < x i) := by
            simpa [add_zero] using not_bdry_strict M 0 x (fun h0 => hb (Or.inl h0))
          have hstrictw : (∀ i : Fin 1, (x + w) i < (M : ℤ)) ∧
              (∀ i : Fin 1, 1 < (x + w) i) ∧
              (∀ i j : Fin 1, i < j → (x + w) j < (x + w) i) :=
            not_bdry_strict M w x (fun hw => hb (Or.inr hw))
          have hx0 : ∀ i : Fin 1,
              inSimplex 1 M (x + unit i) ∧ inSimplex 1 M (x - unit i) := fun i =>
            ⟨inSimplex_add_unit 1 M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i,
              inSimplex_sub_unit 1 M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i⟩
          have hxwS : inSimplex 1 M (x + w) :=
            inSimplex_of_strict M (x + w) hstrictw.1 hstrictw.2.1 hstrictw.2.2
          have hxw : ∀ i : Fin 1,
              inSimplex 1 M (x + w + unit i) ∧ inSimplex 1 M (x + w - unit i) :=
            fun i =>
              ⟨inSimplex_add_unit 1 M (x + w) hxwS hstrictw.1 hstrictw.2.1
                  hstrictw.2.2 i,
                inSimplex_sub_unit 1 M (x + w) hxwS hstrictw.1 hstrictw.2.1
                  hstrictw.2.2 i⟩
          exact difference_interior_step 1 M (by omega) (2 : ℤ) (by omega) (by omega)
            w g hg s x hx hx0 hxw (inSimplex_inCube 1 M (x + w) hxwS) hprev
  have h := hmain t le_rfl y hyS
  simpa [w, e, g, add_assoc] using h

end DimRed
