/-
The iterated one-dimensional self-similarity clause and the lower bound on
successive toppling times from `dimred.tex:915-918` and `1040-1044`.
-/
import DimRed.Support.OneDimConsist
import DimRed.Support.ToppleTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

theorem odo_one_consist_all
    (M j t : ℕ) (_hM : 2 ≤ M) (hj : 1 ≤ j) (hjm : j ≤ M)
    (ht : (t : ℕ∞) ≤ toppleTime 1 j)
    (hmono : ∀ {a b : ℕ}, j ≤ a → a ≤ b →
      toppleTime 1 a ≤ toppleTime 1 b)
    (hprev : ∀ K : ℕ, j < K → ∀ t' : ℕ, t' < t → ∀ z : Site 1,
      2 ≤ z 0 → z 0 ≤ (K : ℤ) →
      odoUnif 1 (2 * K) t' z =
        odoUnif 1 (2 * (K - 1)) t' (fun _ => z 0 - 1))
    (hfacet : ∀ K : ℕ, j < K → ∀ s : ℕ, s + 2 = t →
      ((s + 1 : ℕ) : ℕ∞) < toppleTime 1 (K - 1) → ∀ z : Site 1,
        odoUnif 1 (2 * (K - 1)) s z =
            odoUnif 1 (2 * (K - 1)) s (z + unit 0) + 1 →
          odoUnif 1 (2 * (K - 1)) (s + 1) z =
            odoUnif 1 (2 * (K - 1)) s z ∧
          odoUnif 1 (2 * (K - 1)) (s + 1) (z + unit 0) =
            odoUnif 1 (2 * (K - 1)) s (z + unit 0) + 1)
    (x : Site 1) (hx : inSimplex 1 M x)
    (hxgt : (M : ℤ) - (j : ℤ) < x 0) :
    odoUnif 1 (2 * M) t x =
      odoUnif 1 (2 * j) t
        (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
  have hchain : ∀ K : ℕ, j ≤ K → ∀ y : ℤ,
      1 ≤ y → y ≤ (K : ℤ) → (K : ℤ) - (j : ℤ) < y →
      odoUnif 1 (2 * K) t (fun _ => y) =
        odoUnif 1 (2 * j) t
          (fun _ => y - ((K : ℤ) - (j : ℤ))) := by
    intro K
    induction K using Nat.strong_induction_on with
    | h K ih =>
        intro hKj y hy1 hyK hygt
        by_cases hKeq : K = j
        · subst K
          simp
        · have hKj' : j < K := by omega
          have hK2 : 2 ≤ K := by omega
          have hKm1 : j ≤ K - 1 := by omega
          have htK : (t : ℕ∞) ≤ toppleTime 1 (K - 1) := by
            exact le_trans ht (hmono (a := j) (b := K - 1) (by omega) hKm1)
          have hstep := odo_one_consist_step K t hK2 htK
            (hprev K hKj') (hfacet K hKj') (fun _ => y) (by omega) hyK
          have hprevK : 1 ≤ y - 1 := by omega
          have hprevK' : y - 1 ≤ (K - 1 : ℕ) := by omega
          have hprevKgt : ((K - 1 : ℕ) : ℤ) - (j : ℤ) < y - 1 := by omega
          have hind := ih (K - 1) (by omega) hKm1 (y - 1)
            hprevK hprevK' hprevKgt
          calc
            odoUnif 1 (2 * K) t (fun _ => y) =
                odoUnif 1 (2 * (K - 1)) t (fun _ => y - 1) := hstep
            _ = odoUnif 1 (2 * j) t
                (fun _ => (y - 1) - ((K - 1 : ℕ) - (j : ℤ))) := hind
            _ = odoUnif 1 (2 * j) t
                (fun _ => y - ((K : ℤ) - (j : ℤ))) := by
              congr 2
              funext i
              omega
  have hxconst : x = fun _ => x 0 := site_one_eq_const x
  rw [hxconst]
  have hx1 : 1 ≤ x 0 := (hx.1 (0 : Fin 1)).1
  have hxM : x 0 ≤ (M : ℤ) := (hx.1 (0 : Fin 1)).2
  have h := hchain M (by omega) (x 0) hx1 hxM hxgt
  simpa using h

theorem toppleTime_succ_lower
    (M : ℕ) (hM : 3 ≤ M)
    (hconsist : ∀ (q : ℕ), (q : ℕ∞) ≤ toppleTime 1 (M - 2) →
      odoUnif 1 (2 * M) q (fun _ => (M : ℤ)) =
          odoUnif 1 (2 * (M - 1)) q (fun _ => ((M - 1 : ℕ) : ℤ)) ∧
      odoUnif 1 (2 * M) q (fun _ => (M : ℤ)) =
          odoUnif 1 (2 * (M - 2)) q (fun _ => ((M - 2 : ℕ) : ℤ)))
    (htopple : ∀ q : ℕ, toppleTime 1 (M - 2) ≤ (q : ℕ∞) →
      simplexMax 1 (M - 1) (fun z =>
        odoUnif 1 (2 * (M - 1)) (q + 2) z -
        odoUnif 1 (2 * (M - 1)) q z) ≤ 1)
    (hhitLow : ∃ n : ℕ, 1 ≤ n ∧
      ((M - 2 : ℕ) : ℤ) ≤ odoUnif 1 (2 * (M - 2)) n
        (cornerPoint 1 (M - 2)))
    (hhitHigh : ∃ n : ℕ, 1 ≤ n ∧
      ((M - 1 : ℕ) : ℤ) ≤ odoUnif 1 (2 * (M - 1)) n
        (cornerPoint 1 (M - 1)))
    (hdouble : ∀ q : ℕ, (q : ℕ∞) = toppleTime 1 (M - 2) →
      ((M - 1 : ℕ) : ℤ) ≤ odoUnif 1 (2 * (M - 1)) (q + 1)
        (cornerPoint 1 (M - 1)) →
      2 ≤ odoUnif 1 (2 * (M - 1)) (q + 2)
          (cornerPoint 1 (M - 1)) -
        odoUnif 1 (2 * (M - 1)) q (cornerPoint 1 (M - 1))) :
    toppleTime 1 (M - 2) + 2 ≤ toppleTime 1 (M - 1) := by
  have hlow : 1 ≤ M - 2 := by omega
  have hhigh : 1 ≤ M - 1 := by omega
  have hlow_ne_top : toppleTime 1 (M - 2) ≠ ⊤ :=
    toppleTime_ne_top 1 (M - 2) (by norm_num) hlow hhitLow
  obtain ⟨q, hq⟩ := (WithTop.ne_top_iff_exists.mp hlow_ne_top)
  have hqle : (q : ℕ∞) ≤ toppleTime 1 (M - 2) := by
    exact le_of_eq hq
  have hcross := hconsist q hqle
  have hlow_hit : ((M - 2 : ℕ) : ℤ) ≤
      odoUnif 1 (2 * (M - 2)) q (fun _ => ((M - 2 : ℕ) : ℤ)) := by
    have hq_ge : toppleTime 1 (M - 2) ≤ (q : ℕ∞) := by
      exact le_of_eq hq.symm
    obtain ⟨n, hnq, hn1, hnval⟩ :=
      (toppleTime_le_iff 1 (M - 2) (by norm_num) hlow hhitLow (q : ℕ∞)).1 hq_ge
    have hq_n : (q : ℕ∞) ≤ (n : ℕ∞) := by
      have htn :=
        (toppleTime_le_iff 1 (M - 2) (by norm_num) hlow hhitLow
          (n : ℕ∞)).2 ⟨n, le_rfl, hn1, hnval⟩
      rw [← hq] at htn
      exact htn
    have hnq' : n ≤ q := ENat.coe_le_coe.mp hnq
    have hqn' : q ≤ n := ENat.coe_le_coe.mp hq_n
    have hn : n = q := Nat.le_antisymm hnq' hqn'
    have hcorner_low : cornerPoint 1 (M - 2) =
        fun _ => ((M - 2 : ℕ) : ℤ) := by
      funext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      simp [cornerPoint]
    simpa [hn, hcorner_low] using hnval
  have hlow_upper :
      odoUnif 1 (2 * (M - 2)) q (fun _ => ((M - 2 : ℕ) : ℤ)) ≤
        ((M - 2 : ℕ) : ℤ) := by
    have hqpos : 1 ≤ q := by
      have h := one_le_toppleTime 1 (M - 2)
      rw [← hq] at h
      exact ENat.coe_le_coe.mp h
    have hprev :
        odoUnif 1 (2 * (M - 2)) (q - 1) (fun _ => ((M - 2 : ℕ) : ℤ)) ≤
          ((M - 2 : ℕ) : ℤ) - 1 := by
      by_cases hqone : q = 1
      · subst q
        simp [odoUnif, odo]
        omega
      · have hqprevpos : 1 ≤ q - 1 := by omega
        have hqprevlt : ((q - 1 : ℕ) : ℕ∞) < toppleTime 1 (M - 2) := by
          rw [← hq]
          exact ENat.coe_lt_coe.mpr (show q - 1 < q by omega)
        have hlt := odo_corner_lt_of_lt_toppleTime 1 (M - 2)
          (by norm_num) hlow (q - 1) hqprevlt hqprevpos
        have hcorner : cornerPoint 1 (M - 2) =
            fun _ => ((M - 2 : ℕ) : ℤ) := by
          funext i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst i
          simp [cornerPoint]
        simpa [hcorner] using hlt
    have hstep := odo_succ_sub_bounds 1 (2 * (M - 2))
      (fun _ => (2 : ℤ)) (q - 1) (fun _ => ((M - 2 : ℕ) : ℤ))
    have hstep' :
        odoUnif 1 (2 * (M - 2)) q (fun _ => ((M - 2 : ℕ) : ℤ)) -
          odoUnif 1 (2 * (M - 2)) (q - 1) (fun _ => ((M - 2 : ℕ) : ℤ)) ≤ 1 := by
      simpa [odoUnif, show q - 1 + 1 = q by omega] using hstep.2
    omega
  have hlow_eq :
      odoUnif 1 (2 * (M - 2)) q (fun _ => ((M - 2 : ℕ) : ℤ)) =
        ((M - 2 : ℕ) : ℤ) :=
    le_antisymm hlow_upper hlow_hit
  have hlarge_eq :
      odoUnif 1 (2 * (M - 1)) q (fun _ => ((M - 1 : ℕ) : ℤ)) =
        ((M - 2 : ℕ) : ℤ) := by
    have h := hcross.1.symm.trans hcross.2
    rw [hlow_eq] at h
    exact h
  have hcorner_high : cornerPoint 1 (M - 1) =
      fun _ => ((M - 1 : ℕ) : ℤ) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [cornerPoint]
  have hcorner_low : cornerPoint 1 (M - 2) =
      fun _ => ((M - 2 : ℕ) : ℤ) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [cornerPoint]
  have hlarge_corner_eq :
      odoUnif 1 (2 * (M - 1)) q (cornerPoint 1 (M - 1)) =
        ((M - 2 : ℕ) : ℤ) := by
    simpa [hcorner_high] using hlarge_eq
  have hhigh_ne_top : toppleTime 1 (M - 1) ≠ ⊤ :=
    toppleTime_ne_top 1 (M - 1) (by norm_num) hhigh hhitHigh
  by_cases htop : toppleTime 1 (M - 1) = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨T, hT⟩ := (WithTop.ne_top_iff_exists.mp hhigh_ne_top)
  have hT_ge : ((M - 1 : ℕ) : ℤ) ≤
      odoUnif 1 (2 * (M - 1)) T (cornerPoint 1 (M - 1)) := by
    have hTle : toppleTime 1 (M - 1) ≤ (T : ℕ∞) := by
      exact le_of_eq hT.symm
    obtain ⟨n, hnT, hn1, hnval⟩ :=
      (toppleTime_le_iff 1 (M - 1) (by norm_num) hhigh hhitHigh (T : ℕ∞)).1 hTle
    have hT_n : (T : ℕ∞) ≤ (n : ℕ∞) := by
      have htn :=
        (toppleTime_le_iff 1 (M - 1) (by norm_num) hhigh hhitHigh
          (n : ℕ∞)).2 ⟨n, le_rfl, hn1, hnval⟩
      rw [← hT] at htn
      exact htn
    have hnT' : n ≤ T := ENat.coe_le_coe.mp hnT
    have hTn' : T ≤ n := ENat.coe_le_coe.mp hT_n
    have hn : n = T := Nat.le_antisymm hnT' hTn'
    simpa [hn] using hnval
  have hqT : q ≤ T := by
    by_contra hnot
    have hTq : T < q := by omega
    have hTlelow : (T : ℕ∞) ≤ toppleTime 1 (M - 2) := by
      exact le_trans (ENat.coe_le_coe.mpr (show T ≤ q by omega)) (le_of_eq hq)
    have hcrossT := hconsist T hTlelow
    have hlowT :
        odoUnif 1 (2 * (M - 2)) T (fun _ => ((M - 2 : ℕ) : ℤ)) <
          ((M - 2 : ℕ) : ℤ) := by
      by_cases hTzero : T = 0
      · subst T
        simp [odoUnif, odo]
        omega
      · have hTpos : 1 ≤ T := by omega
        have hTlt : (T : ℕ∞) < toppleTime 1 (M - 2) := by
          exact (ENat.coe_lt_coe.mpr hTq).trans_eq hq
        have hlt := odo_corner_lt_of_lt_toppleTime 1 (M - 2)
          (by norm_num) hlow T hTlt hTpos
        have hcorner := hcorner_low
        simpa [hcorner] using hlt
    have hlargeT :
        odoUnif 1 (2 * (M - 1)) T (cornerPoint 1 (M - 1)) <
          ((M - 1 : ℕ) : ℤ) := by
      have h := hcrossT.1.symm.trans hcrossT.2
      have h' :
          odoUnif 1 (2 * (M - 1)) T (cornerPoint 1 (M - 1)) =
            odoUnif 1 (2 * (M - 2)) T (cornerPoint 1 (M - 2)) := by
        simpa [hcorner_low, hcorner_high] using h
      rw [h', hcorner_low]
      omega
    linarith [hT_ge, hlargeT]
  have hTneq_q : T ≠ q := by
    intro hTq
    subst T
    omega
  have hTneq_q1 : T ≠ q + 1 := by
    intro hTq
    have hnext := hdouble q hq (by simpa [hTq] using hT_ge)
    have hsimplex : inSimplex 1 (M - 1) (cornerPoint 1 (M - 1)) := by
      rw [hcorner_high]
      constructor
      · intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst i
        have hm1 : 1 ≤ M - 1 := by omega
        change (1 : ℤ) ≤ ((M - 1 : ℕ) : ℤ) ∧
          ((M - 1 : ℕ) : ℤ) ≤ ((M - 1 : ℕ) : ℤ)
        exact ⟨by exact_mod_cast hm1, le_rfl⟩
      · intro i j _
        exact le_rfl
    have hstrong := htopple q (le_of_eq hq.symm)
    have hbound := le_simplexMax 1 (M - 1) (fun z =>
      odoUnif 1 (2 * (M - 1)) (q + 2) z -
        odoUnif 1 (2 * (M - 1)) q z) (cornerPoint 1 (M - 1)) hsimplex
    have hstrong' :
        odoUnif 1 (2 * (M - 1)) (q + 2) (cornerPoint 1 (M - 1)) -
            odoUnif 1 (2 * (M - 1)) q (cornerPoint 1 (M - 1)) ≤ 1 :=
      le_trans hbound hstrong
    linarith [hnext, hstrong']
  have hq2T : q + 2 ≤ T := by omega
  calc
    toppleTime 1 (M - 2) + 2 = (q : ℕ∞) + 2 := by rw [← hq]; rfl
    _ = ((q + 2 : ℕ) : ℕ∞) := by
      norm_num [ENat.coe_add]
    _ ≤ (T : ℕ∞) := ENat.coe_le_coe.mpr hq2T
    _ = toppleTime 1 (M - 1) := hT

end DimRed
