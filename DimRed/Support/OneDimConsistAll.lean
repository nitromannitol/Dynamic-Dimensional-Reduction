module

/-
The iterated one-dimensional self-similarity clause and the lower bound on
successive toppling times from `dimred-corrected-arxiv.tex`, labels `base_dimension` and `subsec:regularity_higher`.
-/
public import DimRed.Support.OneDimConsist
public import DimRed.Support.CornerReaches
public import DimRed.Support.EarlyTimes
public import DimRed.Support.StrongDerivPure
public import DimRed.Support.ToppleTime

@[expose] public section

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
    (hmono : ∀ {a b : ℕ}, j ≤ a → a ≤ b → b < M →
      toppleTime 1 a ≤ toppleTime 1 b)
    (hprev : ∀ K : ℕ, j < K → K ≤ M → ∀ t' : ℕ, t' < t → ∀ z : Site 1,
      2 ≤ z 0 → z 0 ≤ (K : ℤ) →
      odoUnif 1 (2 * K) t' z =
        odoUnif 1 (2 * (K - 1)) t' (fun _ => z 0 - 1))
    (hfacet : ∀ K : ℕ, j < K → K ≤ M → ∀ s : ℕ, s + 2 = t →
      ((s + 1 : ℕ) : ℕ∞) < toppleTime 1 (K - 1) →
        odoUnif 1 (2 * (K - 1)) s (fun _ => (1 : ℤ)) =
            odoUnif 1 (2 * (K - 1)) s (fun _ => (2 : ℤ)) + 1 →
          odoUnif 1 (2 * (K - 1)) (s + 1) (fun _ => (1 : ℤ)) =
            odoUnif 1 (2 * (K - 1)) s (fun _ => (1 : ℤ)) ∧
          odoUnif 1 (2 * (K - 1)) (s + 1) (fun _ => (2 : ℤ)) =
            odoUnif 1 (2 * (K - 1)) s (fun _ => (2 : ℤ)) + 1)
    (x : Site 1) (hx : inSimplex 1 M x)
    (hxgt : (M : ℤ) - (j : ℤ) < x 0) :
    odoUnif 1 (2 * M) t x =
      odoUnif 1 (2 * j) t
        (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
  have hchain : ∀ K : ℕ, j ≤ K → K ≤ M → ∀ y : ℤ,
      1 ≤ y → y ≤ (K : ℤ) → (K : ℤ) - (j : ℤ) < y →
      odoUnif 1 (2 * K) t (fun _ => y) =
        odoUnif 1 (2 * j) t
          (fun _ => y - ((K : ℤ) - (j : ℤ))) := by
    intro K
    induction K using Nat.strong_induction_on with
    | h K ih =>
        intro hKj hKM y hy1 hyK hygt
        by_cases hKeq : K = j
        · subst K
          simp
        · have hKj' : j < K := by omega
          have hK2 : 2 ≤ K := by omega
          have hKm1 : j ≤ K - 1 := by omega
          have htK : (t : ℕ∞) ≤ toppleTime 1 (K - 1) := by
            exact le_trans ht (hmono (a := j) (b := K - 1) (by omega) hKm1 (by omega))
          have hstep := odo_one_consist_step K t hK2 htK
            (hprev K hKj' hKM) (hfacet K hKj' hKM) (fun _ => y) (by omega) hyK
          have hprevK : 1 ≤ y - 1 := by omega
          have hprevK' : y - 1 ≤ (K - 1 : ℕ) := by omega
          have hprevKgt : ((K - 1 : ℕ) : ℤ) - (j : ℤ) < y - 1 := by omega
          have hind := ih (K - 1) (by omega) hKm1 (by omega) (y - 1)
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
  have h := hchain M (by omega) (le_refl M) (x 0) hx1 hxM hxgt
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
    have hnq' : n ≤ q := ENat.natCast_le_natCast.mp hnq
    have hqn' : q ≤ n := ENat.natCast_le_natCast.mp hq_n
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
      exact ENat.natCast_le_natCast.mp h
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
          exact ENat.natCast_lt_natCast.mpr (show q - 1 < q by omega)
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
    have hnT' : n ≤ T := ENat.natCast_le_natCast.mp hnT
    have hTn' : T ≤ n := ENat.natCast_le_natCast.mp hT_n
    have hn : n = T := Nat.le_antisymm hnT' hTn'
    simpa [hn] using hnval
  have hqT : q ≤ T := by
    by_contra hnot
    have hTq : T < q := by omega
    have hTlelow : (T : ℕ∞) ≤ toppleTime 1 (M - 2) := by
      exact le_trans (ENat.natCast_le_natCast.mpr (show T ≤ q by omega)) (le_of_eq hq)
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
          exact (ENat.natCast_lt_natCast.mpr hTq).trans_eq hq
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
      norm_num [ENat.natCast_add]
    _ ≤ (T : ℕ∞) := ENat.natCast_le_natCast.mpr hq2T
    _ = toppleTime 1 (M - 1) := hT

/-- The `hdouble` input of `toppleTime_succ_lower` is vacuously true.  At the
topple time `q` of the cube of half-side `M-2`, the corner of the cube of
half-side `M-1` has exactly `M-2` topples; if it reached `M-1` one step later it
would have toppled at `q`, forcing `v_q(M-2) = 2(M-2)` by the derivative bound
at scale `M-1`, while self-similarity at scale `M-1` and the derivative bound at
scale `M-2` force `v_q(M-2) ≤ 2(M-2) - 1`. -/
theorem one_dim_double (M q : ℕ) (hM : 4 ≤ M)
    (hq : (q : ℕ∞) = toppleTime 1 (M - 2))
    (hconsist : ∀ (j : ℕ), 1 ≤ j → j ≤ M - 1 → (q : ℕ∞) ≤ toppleTime 1 j →
      ∀ x : Site 1, inSimplex 1 (M - 1) x →
        (∀ i : Fin 1, ((M - 1 : ℕ) : ℤ) - (j : ℤ) < x i) →
        odoUnif 1 (2 * (M - 1)) q x =
          odoUnif 1 (2 * j) q (fun i => x i - (((M - 1 : ℕ) : ℤ) - (j : ℤ))))
    (hlarge_eq : odoUnif 1 (2 * (M - 1)) q (fun _ => ((M - 1 : ℕ) : ℤ))
      = ((M - 2 : ℕ) : ℤ))
    (hreach : ((M - 1 : ℕ) : ℤ) ≤ odoUnif 1 (2 * (M - 1)) (q + 1)
      (cornerPoint 1 (M - 1))) :
    2 ≤ odoUnif 1 (2 * (M - 1)) (q + 2) (cornerPoint 1 (M - 1)) -
      odoUnif 1 (2 * (M - 1)) q (cornerPoint 1 (M - 1)) := by
  exfalso
  have hcorner : cornerPoint 1 (M - 1) = (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [cornerPoint]
    simp
  rw [hcorner] at hreach
  -- the corner topples at `q + 1`, so its sandpile at `q` is at least two
  have hcube : inCube 1 (2 * (M - 1)) (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) := by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul]
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
    omega
  have hstep := odo_succ_eq 1 (2 * (M - 1)) (fun _ => 2) q
    (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) hcube
  norm_num at hstep
  have hlarge : odo 1 (2 * (M - 1)) (fun _ => 2) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      = ((M - 2 : ℕ) : ℤ) := by
    have h := hlarge_eq
    simp only [odoUnif] at h
    norm_num at h
    exact h
  have hreach' : ((M - 1 : ℕ) : ℤ) ≤ odo 1 (2 * (M - 1)) (fun _ => 2) (q + 1)
      (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) := by
    have h := hreach
    simp only [odoUnif] at h
    norm_num at h
    exact h
  -- `v_{q+1} ≤ v_q + 1`, so `v_{q+1} = M - 1` and the corner topples at `q`
  have hbound := (odo_succ_sub_bounds 1 (2 * (M - 1)) (fun _ => 2) q
    (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))).2
  have htopple : 2 * (1 : ℤ) ≤ sandp 1 (2 * (M - 1)) (fun _ => 2) q
      (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) := by
    by_contra hcon
    push Not at hcon
    rw [ite_eq_right (show ¬ (2 ≤ sandp 1 (2 * (M - 1)) (fun _ => 2) q
      (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))) from not_le.mpr hcon)] at hstep
    rw [hlarge] at hstep
    omega
  -- the sandpile at the corner is `2 - 2 v_q(M-1) + v_q(M-2)`
  have hsand : sandp 1 (2 * (M - 1)) (fun _ => 2) q
      (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      = 2 - 2 * odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
        + odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
    rw [sandp, lap]
    norm_num
    have hnbr : nbrSum (odo 1 (2 * (M - 1)) (fun _ => 2) q)
        (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
        = odo 1 (2 * (M - 1)) (fun _ => 2) q (fun _ => ((M - 1 : ℕ) : ℤ) + 1)
          + odo 1 (2 * (M - 1)) (fun _ => 2) q (fun _ => ((M - 1 : ℕ) : ℤ) - 1) := by
      simp only [nbrSum, Fin.sum_univ_one]
      rw [site_one_add_unit, site_one_sub_unit]
    rw [hnbr]
    have hoff : ¬ inCube 1 (2 * (M - 1)) (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ) + 1) := by
      intro hc
      have h := hc ⟨0, by omega⟩
      rw [loCoord_two_mul, hiCoord_two_mul] at h
      rw [Nat.cast_sub (by omega : 1 ≤ M)] at h
      simp only at h
      omega
    rw [odo_eq_zero_outside 1 (2 * (M - 1)) (fun _ => 2) q _ hoff]
    have hinner : (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ) - 1)
        = (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
      funext i
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ M)]
        norm_num
      rw [hM2]
      ring
    rw [hinner]
    simp only [odoUnif]
    norm_num
    ring
  -- so `v_q(M-2) ≥ 2(M-2)`
  have hlow : 2 * ((M - 2 : ℕ) : ℤ)
      ≤ odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
    have hlarge' : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
        = ((M - 2 : ℕ) : ℤ) := hlarge_eq
    rw [hsand, hlarge'] at htopple
    linarith
  -- and the derivative bound at scale `M-1` gives the reverse inequality
  have hderiv : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      - odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      ≤ ((M - 2 : ℕ) : ℤ) := by
    have h := odo_first_diff 1 (M - 1) (by norm_num) (by omega) q
      (⟨0, by omega⟩ : Fin 1) (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) (by
        have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ M)]
          norm_num
        rw [hM2]
        omega)
    have hpt : (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) + unit (⟨0, by omega⟩ : Fin 1)
        = (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ)) := by
      funext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [Pi.add_apply]
      have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ M)]
        norm_num
      rw [hM2, Nat.cast_sub (by omega : 1 ≤ M)]
      simp [unit]
      ring
    rw [hpt] at h
    exact h
  -- the self-similarity clause at scale `M-1` with `j = M-2`
  have hqle : (q : ℕ∞) ≤ toppleTime 1 (M - 2) := le_of_eq hq
  have hsim : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      = odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ)) := by
    have h := hconsist (M - 2) (by omega) (by omega) hqle
      (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      (by
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          have h1 : (1 : ℤ) ≤ ((M - 2 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : 2 ≤ M)]
            norm_num
            omega
          have h2 : ((M - 2 : ℕ) : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : 2 ≤ M), Nat.cast_sub (by omega : 1 ≤ M)]
            norm_num
          exact ⟨h1, h2⟩
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj])
      (fun i => by
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        change ((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ) < ((M - 2 : ℕ) : ℤ)
        have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ M)]
          norm_num
        rw [Nat.cast_sub (by omega : 1 ≤ M), hM2]
        omega)
    have hpt : (fun i : Fin 1 => ((M - 2 : ℕ) : ℤ) - (((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ)))
        = (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ)) := by
      funext i
      have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ M)]
        norm_num
      have hM3 : ((M - 3 : ℕ) : ℤ) = (M : ℤ) - 3 := by
        rw [Nat.cast_sub (by omega : 3 ≤ M)]
        norm_num
      rw [Nat.cast_sub (by omega : 1 ≤ M), hM2, hM3]
      ring
    rw [hpt] at h
    exact h
  -- the corner of the smaller cube at its topple time
  have hsim2 : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      = odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
    have h := hconsist (M - 2) (by omega) (by omega) hqle
      (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      (by
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          have h1 : (1 : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ M)]
            norm_num
            omega
          exact ⟨h1, le_refl _⟩
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj])
      (fun i => by
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        change ((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ) < ((M - 1 : ℕ) : ℤ)
        have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ M)]
          norm_num
        rw [Nat.cast_sub (by omega : 1 ≤ M), hM2]
        omega)
    have hpt : (fun i : Fin 1 => ((M - 1 : ℕ) : ℤ) - (((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ)))
        = (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
      funext i
      have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ M)]
        norm_num
      rw [Nat.cast_sub (by omega : 1 ≤ M), hM2]
      ring
    rw [hpt] at h
    exact h
  -- the derivative bound at scale `M-2`
  have hderiv2 : odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ))
      - odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      ≤ ((M - 3 : ℕ) : ℤ) := by
    have h := odo_first_diff 1 (M - 2) (by norm_num) (by omega) q
      (⟨0, by omega⟩ : Fin 1) (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ)) (by
        have hM3 : ((M - 3 : ℕ) : ℤ) = (M : ℤ) - 3 := by
          rw [Nat.cast_sub (by omega : 3 ≤ M)]
          norm_num
        rw [hM3]
        omega)
    have hpt : (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ)) + unit (⟨0, by omega⟩ : Fin 1)
        = (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
      funext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [Pi.add_apply]
      have hM3 : ((M - 3 : ℕ) : ℤ) = (M : ℤ) - 3 := by
        rw [Nat.cast_sub (by omega : 3 ≤ M)]
        norm_num
      have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ M)]
        norm_num
      rw [hM3, hM2]
      simp [unit]
      ring
    rw [hpt] at h
    exact h
  -- combine: `2(M-2) ≤ v_q(M-2) ≤ 2(M-2) - 1`
  have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ M)]
    norm_num
  have hM3 : ((M - 3 : ℕ) : ℤ) = (M : ℤ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ M)]
    norm_num
  have hlarge'' : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
      = ((M - 2 : ℕ) : ℤ) := hlarge_eq
  -- `v_q^{(M-1)}(M-2) = 2(M-2)`
  have hEq : odoUnif 1 (2 * (M - 1)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      = 2 * ((M - 2 : ℕ) : ℤ) := by
    have h := hderiv
    rw [hlarge''] at h
    linarith
  -- so `v_q^{(M-2)}(M-3) = 2(M-2)`
  have hEq2 : odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 3 : ℕ) : ℤ))
      = 2 * ((M - 2 : ℕ) : ℤ) := by
    rw [← hsim]
    exact hEq
  -- and `v_q^{(M-2)}(M-2) = M-2`
  have hEq3 : odoUnif 1 (2 * (M - 2)) q (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
      = ((M - 2 : ℕ) : ℤ) := by
    rw [← hsim2]
    exact hlarge''
  rw [hEq2, hEq3] at hderiv2
  rw [hM2, hM3] at hderiv2
  linarith

/-- The sandpile at the corner of the cube of side four at time one is one. -/
theorem sandp_corner_one : sandp 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
  rw [sandp, lap]
  norm_num
  have hnbr : nbrSum (odo 1 4 (fun _ => 2) 1) (fun _ : Fin 1 => (2 : ℤ))
      = odo 1 4 (fun _ => 2) 1 (fun _ => (3 : ℤ))
        + odo 1 4 (fun _ => 2) 1 (fun _ => (1 : ℤ)) := by
    simp only [nbrSum, Fin.sum_univ_one]
    rw [site_one_add_unit, site_one_sub_unit]
    norm_num
  rw [hnbr]
  have h1 : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (2 : ℤ)) (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  rw [h1]
  have hoff : ¬ inCube 1 4 (fun _ : Fin 1 => (3 : ℤ)) := by
    intro hc
    have h := hc ⟨0, by omega⟩
    rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul] at h
    norm_num at h
  rw [odo_eq_zero_outside 1 4 (fun _ => 2) 1 _ hoff]
  have hone : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (1 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (1 : ℤ)) (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  rw [hone]
  norm_num

/-- The sandpile at the corner of the cube of side four at time one, at the
neighbouring site, is at least two. -/
theorem sandp_corner_one_neighbour :
    2 ≤ sandp 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (1 : ℤ)) := by
  rw [sandp, lap]
  have hnbr1 : nbrSum (odo 1 4 (fun _ => 2) 1) (fun _ : Fin 1 => (1 : ℤ))
      = odo 1 4 (fun _ => 2) 1 (fun _ => (2 : ℤ))
        + odo 1 4 (fun _ => 2) 1 (fun _ => (0 : ℤ)) := by
    simp only [nbrSum, Fin.sum_univ_one]
    rw [site_one_add_unit, site_one_sub_unit]
    norm_num
  have h1' : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (1 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (1 : ℤ)) (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  have hzero : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (0 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (0 : ℤ)) (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  have h2' : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (2 : ℤ)) (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  rw [hnbr1, h1', hzero, h2']
  norm_num
/-- The sandpile at the corner of the cube of side four at time two is at
least two, so the corner topples at time three. -/
theorem sandp_corner_two :
    2 ≤ sandp 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (2 : ℤ)) := by
  have hcube : inCube 1 4 (fun _ : Fin 1 => (2 : ℤ)) := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
    norm_num
  have h1 : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (2 : ℤ)) hcube
    have h' := h
    simp only [odoUnif] at h'
    norm_num at h'
    exact h'
  have h2 : odo 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    rw [odo_succ_eq 1 4 (fun _ => 2) 1 _ hcube, h1]
    rw [ite_eq_right (by rw [sandp_corner_one]; norm_num)]
    norm_num
  rw [sandp, lap]
  rw [h2]
  have hnbr : nbrSum (odo 1 4 (fun _ => 2) 2) (fun _ : Fin 1 => (2 : ℤ))
      = odo 1 4 (fun _ => 2) 2 (fun _ => (3 : ℤ))
        + odo 1 4 (fun _ => 2) 2 (fun _ => (1 : ℤ)) := by
    simp only [nbrSum, Fin.sum_univ_one]
    rw [site_one_add_unit, site_one_sub_unit]
    norm_num
  rw [hnbr]
  have hoff : ¬ inCube 1 4 (fun _ : Fin 1 => (3 : ℤ)) := by
    intro hc
    have h := hc ⟨0, by omega⟩
    rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul] at h
    norm_num at h
  rw [odo_eq_zero_outside 1 4 (fun _ => 2) 2 _ hoff]
  have hone : 2 ≤ odo 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (1 : ℤ)) := by
    rw [odo_succ_eq 1 4 (fun _ => 2) 1 _ (by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
      norm_num)]
    have h1' : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (1 : ℤ)) = 1 := by
      have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (1 : ℤ)) (by
        intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
        norm_num)
      have h' := h
      simp only [odoUnif] at h'
      norm_num at h'
      exact h'
    rw [h1']
    norm_num
    rw [ite_eq_left sandp_corner_one_neighbour]
    norm_num
  norm_num at hone ⊢
  linarith [hone]
theorem toppleTime_one_two : toppleTime 1 2 = 3 := by
  have hc : cornerPoint 1 2 = (fun _ : Fin 1 => (2 : ℤ)) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [cornerPoint]
    simp
  have hcube : inCube 1 4 (fun _ : Fin 1 => (2 : ℤ)) := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
    norm_num
  have h1 : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    simp only [odo]
    rw [ite_eq_left hcube]
    norm_num [lap, nbrSum, Fin.sum_univ_one, unit]
  have h2 : odo 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
    rw [odo_succ_eq 1 4 (fun _ => 2) 1 _ hcube, h1]
    rw [ite_eq_right (by rw [sandp_corner_one]; norm_num)]
    norm_num
  have h3 : 2 ≤ odo 1 4 (fun _ => 2) 3 (fun _ : Fin 1 => (2 : ℤ)) := by
    rw [odo_succ_eq 1 4 (fun _ => 2) 2 _ hcube, h2]
    norm_num
    rw [ite_eq_left sandp_corner_two]
    norm_num
  have hle : toppleTime 1 2 ≤ 3 := by
    rw [toppleTime_eq_corner 1 2 (by norm_num) (by omega)]
    apply sInf_le
    exact ⟨3, ⟨by norm_num, by rw [hc]; exact h3⟩, rfl⟩
  have hgt : ¬ (toppleTime 1 2 ≤ 2) := by
    intro hcon
    have hmem := (toppleTime_le_iff 1 2 (by norm_num) (by omega)
      ⟨3, by norm_num, by rw [hc]; exact h3⟩ (2 : ℕ∞)).mp hcon
    obtain ⟨n, hn, hn1, hnval⟩ := hmem
    have hn2 : n ≤ 2 := ENat.natCast_le_natCast.mp hn
    -- the odometer is monotone in time, so it is at most one for `n ≤ 2`
    have hmono : odoUnif 1 4 n (fun _ : Fin 1 => (2 : ℤ))
        ≤ odoUnif 1 4 2 (fun _ : Fin 1 => (2 : ℤ)) :=
      odo_mono 1 4 (fun _ => 2) hn2 _
    have h2u : odoUnif 1 4 2 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
      change odo 1 4 (fun _ => 2 * (1 : ℤ)) 2 (fun _ : Fin 1 => (2 : ℤ)) = 1
      norm_num
      exact h2
    rw [h2u] at hmono
    rw [hc] at hnval
    have hnval' : (2 : ℤ) ≤ odoUnif 1 4 n (fun _ : Fin 1 => (2 : ℤ)) := hnval
    linarith
  -- `τ_2 ≤ 3` and `τ_2 > 2`, so `τ_2 = 3`
  -- `τ_2 ≤ 3` and `τ_2 > 2`, so `τ_2 = 3`
  have hge : 3 ≤ toppleTime 1 2 := by
    by_contra hcon
    push Not at hcon
    -- `τ_2 < 3` and `τ_2 ≤ 3` make `τ_2` a natural number below three
    obtain ⟨T, hT, _⟩ := (WithTop.le_coe_iff).mp hle
    rw [hT] at hcon
    have hT3 : T < 3 := ENat.natCast_lt_natCast.mp hcon
    have hT2 : T ≤ 2 := by omega
    exact hgt (by rw [hT]; exact ENat.natCast_le_natCast.mpr hT2)
  exact le_antisymm hle hge
theorem one_dim_tau_gap (M t : ℕ) (hM : 3 ≤ M) (ht : toppleTime 1 (M - 1) ≤ (t : ℕ∞))
    (hconsist : RegConsist 1 M t)
    (hclause : ∀ q' : ℕ, (q' : ℕ∞) ≤ toppleTime 1 (M - 2) →
      odoUnif 1 (2 * M) q' (fun _ => (M : ℤ))
          = odoUnif 1 (2 * (M - 1)) q' (fun _ => ((M - 1 : ℕ) : ℤ)) ∧
        odoUnif 1 (2 * M) q' (fun _ => (M : ℤ))
          = odoUnif 1 (2 * (M - 2)) q' (fun _ => ((M - 2 : ℕ) : ℤ)))
    (hprior : ∀ d' M' t' : ℕ, regEarlier 1 M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    toppleTime 1 (M - 2) + 2 ≤ toppleTime 1 (M - 1) := by
  refine toppleTime_succ_lower M hM ?_ ?_ ?_ ?_ ?_
  · intro q' hq'
    -- the clause at scale `M` at time `q'`: either `q' < t`, where the earlier
    -- instances supply it, or `q' = t`, where the triple's own consistency
    -- clause does
    exact hclause q' hq'
  · intro q' hq'
    have h := (hprior 1 (M - 1) q' (Or.inr (Or.inl ⟨rfl, by omega⟩))
      (by omega) (by omega)).1.2.2.2.2
    exact h hq'
  · exact corner_reaches 1 (M - 2) (by norm_num) (by omega)
      (fun e he hed t y hy => by omega)
  · exact corner_reaches 1 (M - 1) (by norm_num) (by omega)
      (fun e he hed t y hy => by omega)
  · intro q' hq' hdbl
    by_cases hM4 : 4 ≤ M
    · exact one_dim_double M q' hM4 hq'
        (fun j hj1 hj2 hqj x hx hxgt => by
          have h := (hprior 1 (M - 1) q' (Or.inr (Or.inl ⟨rfl, by omega⟩))
            (by omega) (by omega)).1.1
          exact h j hj1 hj2 hqj x hx hxgt)
        (by
          have h := (hprior 1 (M - 1) q' (Or.inr (Or.inl ⟨rfl, by omega⟩))
            (by omega) (by omega)).1.1 (M - 2) (by omega) (by omega)
            (by rw [hq'])
            (fun _ : Fin 1 => ((M - 1 : ℕ) : ℤ))
            (by
              constructor
              · intro i
                have hi : i = (0 : Fin 1) := Fin.eq_zero i
                subst hi
                have h1 : (1 : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by
                  rw [Nat.cast_sub (by omega : 1 ≤ M)]
                  norm_num
                  omega
                exact ⟨h1, le_refl _⟩
              · intro i j _
                have hi : i = (0 : Fin 1) := Fin.eq_zero i
                have hj : j = (0 : Fin 1) := Fin.eq_zero j
                rw [hi, hj])
            (fun i => by
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst hi
              change ((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ) < ((M - 1 : ℕ) : ℤ)
              have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
                rw [Nat.cast_sub (by omega : 2 ≤ M)]
                norm_num
              rw [Nat.cast_sub (by omega : 1 ≤ M), hM2]
              omega)
          have hpt : (fun i : Fin 1 => ((M - 1 : ℕ) : ℤ) - (((M - 1 : ℕ) : ℤ) - ((M - 2 : ℕ) : ℤ)))
              = (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
            funext i
            have hM2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
              rw [Nat.cast_sub (by omega : 2 ≤ M)]
              norm_num
            rw [Nat.cast_sub (by omega : 1 ≤ M), hM2]
            ring
          rw [hpt] at h
          -- `v_{q'}^{(M-1)}(M-1) = v_{q'}^{(M-2)}(M-2)`, and the smaller cube's
          -- corner at its own topple time is `M-2`
          have hval : odoUnif 1 (2 * (M - 2)) q' (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
              = ((M - 2 : ℕ) : ℤ) := by
            have hc := (hclause q' (le_of_eq hq')).2
            -- the smaller cube's corner at its own topple time is `M-2`
            -- the smaller cube's corner at its own topple time is `M-2`
            have hhit : ∃ n : ℕ, 1 ≤ n ∧
                ((M - 2 : ℕ) : ℤ) ≤ odoUnif 1 (2 * (M - 2)) n
                  (cornerPoint 1 (M - 2)) := by
              exact corner_reaches 1 (M - 2) (by norm_num) (by omega)
                (fun e he hel t y hy => by
                  have he0 : e = 0 := by omega
                  subst he0
                  exact (hprior 1 (M - 2) t (Or.inr (Or.inl ⟨rfl, by omega⟩))
                    (by omega) (by omega)).2 0 (by omega) rfl y hy)
            have hle := (toppleTime_le_iff 1 (M - 2) (by norm_num) (by omega) hhit
              (q' : ℕ∞)).mp (le_of_eq hq'.symm)
            obtain ⟨n, hn, hn1, hnval⟩ := hle
            have hq'le : (q' : ℕ∞) ≤ toppleTime 1 (M - 2) := le_of_eq hq'
            have hnq : n ≤ q' := ENat.natCast_le_natCast.mp hn
            have hmono : odoUnif 1 (2 * (M - 2)) n (cornerPoint 1 (M - 2))
                ≤ odoUnif 1 (2 * (M - 2)) q' (cornerPoint 1 (M - 2)) :=
              odo_mono 1 (2 * (M - 2)) (fun _ => 2) hnq (cornerPoint 1 (M - 2))
            have hcorner : cornerPoint 1 (M - 2) = (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ)) := by
              funext i
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst hi
              rw [cornerPoint]
              simp
            rw [hcorner] at hmono hnval
            have hup : odoUnif 1 (2 * (M - 2)) q' (fun _ : Fin 1 => ((M - 2 : ℕ) : ℤ))
                ≤ ((M - 2 : ℕ) : ℤ) := by
              have h := odo_corner_le_M 1 (M - 2) (by norm_num) (by omega) q'
              rw [hcorner] at h
              exact h
            exact le_antisymm hup (le_trans hnval hmono)
          rw [hval] at h
          exact h)
        hdbl
    · -- M = 3: the gap is `τ_1 + 2 ≤ τ_2`
      have hM3' : M = 3 := by omega
      subst hM3'
      norm_num
      -- `q' = τ_1 = 1`, and the corner of the side-four cube reaches two at
      -- time three, so the difference over two steps is two
      have hq1 : q' = 1 := by
        have h1 : toppleTime 1 1 = 1 := by
          apply le_antisymm
          · rw [toppleTime_eq_corner 1 1 (by norm_num) (by omega)]
            apply sInf_le
            exact ⟨1, ⟨by norm_num, corner_one_le 1⟩, rfl⟩
          · exact one_le_toppleTime 1 1
        have hle : q' ≤ 1 := by
          have h2 : (q' : ℕ∞) ≤ toppleTime 1 (3 - 2) := le_of_eq hq'
          rw [show (3 : ℕ) - 2 = 1 by norm_num, h1] at h2
          exact ENat.natCast_le_natCast.mp h2
        have hge : 1 ≤ q' := by
          have h2 : (1 : ℕ∞) ≤ (q' : ℕ∞) := by
            rw [hq']
            exact one_le_toppleTime 1 (3 - 2)
          exact ENat.natCast_le_natCast.mp h2
        omega
      subst hq1
      have hc : cornerPoint 1 2 = (fun _ : Fin 1 => (2 : ℤ)) := by
        funext i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        rw [cornerPoint]
        simp
      have hcube : inCube 1 4 (fun _ : Fin 1 => (2 : ℤ)) := by
        intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        rw [show (4 : ℕ) = 2 * 2 by norm_num, loCoord_two_mul, hiCoord_two_mul]
        norm_num
      have h1v : odo 1 4 (fun _ => 2) 1 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
        have h := odoUnif_one 1 4 (by norm_num) (fun _ : Fin 1 => (2 : ℤ)) hcube
        have h' := h
        simp only [odoUnif] at h'
        norm_num at h'
        exact h'
      have h2v : odo 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (2 : ℤ)) = 1 := by
        rw [odo_succ_eq 1 4 (fun _ => 2) 1 _ hcube, h1v]
        rw [ite_eq_right (by rw [sandp_corner_one]; norm_num)]
        norm_num
      have h3v : 2 ≤ odo 1 4 (fun _ => 2) 3 (fun _ : Fin 1 => (2 : ℤ)) := by
        rw [odo_succ_eq 1 4 (fun _ => 2) 2 _ hcube, h2v]
        norm_num
        rw [ite_eq_left sandp_corner_two]
        norm_num
      rw [hc]
      -- the hypothesis `hdbl` is false at `M = 3`: the corner of the side-four
      -- cube has only one topple at time two
      exfalso
      have hdbl' := hdbl
      rw [show (1 : ℕ) + 1 = 2 by norm_num] at hdbl'
      rw [show cornerPoint 1 2 = (fun _ : Fin 1 => (2 : ℤ)) from hc] at hdbl'
      rw [show odoUnif 1 (2 * 2) 2 (fun _ : Fin 1 => (2 : ℤ))
          = odo 1 4 (fun _ => 2) 2 (fun _ : Fin 1 => (2 : ℤ)) from rfl] at hdbl'
      rw [h2v] at hdbl'
      norm_num at hdbl'
/-- The corner odometer of the side-`b` cube is at most the corner odometer of
the side-`a` cube plus `b - a`, for `a ≤ b` and `n ≤ τ_a`. -/
theorem odo_corner_dominate (a b n : ℕ) (hab : a ≤ b) (_ha : 1 ≤ a)
    (htau : (n : ℕ∞) ≤ toppleTime 1 a)
    (hmono : ∀ {c d : ℕ}, a ≤ c → c ≤ d → toppleTime 1 c ≤ toppleTime 1 d)
    (hconsist : ∀ K : ℕ, a < K → K ≤ b → (n : ℕ∞) ≤ toppleTime 1 (K - 1) →
      odoUnif 1 (2 * K) n (cornerPoint 1 K) ≤
        odoUnif 1 (2 * (K - 1)) n (cornerPoint 1 (K - 1)) + 1) :
    odoUnif 1 (2 * b) n (cornerPoint 1 b) ≤
      odoUnif 1 (2 * a) n (cornerPoint 1 a) + ((b - a : ℕ) : ℤ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have h1 := hconsist (b + 1) (by omega) (by omega)
      (le_trans htau (hmono (by omega) (by omega)))
    rw [show b + 1 - 1 = b by omega] at h1
    have h2 : odoUnif 1 (2 * b) n (cornerPoint 1 b) ≤
        odoUnif 1 (2 * a) n (cornerPoint 1 a) + ((b - a : ℕ) : ℤ) :=
      ih (fun K hK hKb => hconsist K hK (by omega))
    have h3 : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by
      have : b + 1 - a = (b - a) + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]
    rw [h3]
    linarith
/-- The topple time is monotone in the scale, from the consistency clause at
the larger scale. -/
theorem toppleTime_mono_scale (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hconsist : ∀ n : ℕ, (n : ℕ∞) ≤ toppleTime 1 a →
      odoUnif 1 (2 * b) n (cornerPoint 1 b) =
        odoUnif 1 (2 * a) n (cornerPoint 1 a))
    (hhitb : ∃ n : ℕ, 1 ≤ n ∧ (b : ℤ) ≤ odoUnif 1 (2 * b) n (cornerPoint 1 b))
    (hhita : ∃ n : ℕ, 1 ≤ n ∧ (a : ℤ) ≤ odoUnif 1 (2 * a) n (cornerPoint 1 a)) :
    toppleTime 1 a ≤ toppleTime 1 b := by
  by_contra hcon
  push Not at hcon
  -- `τ_b < τ_a`
  have hb1 : 1 ≤ b := le_trans ha hab
  have hne : toppleTime 1 b ≠ ⊤ := toppleTime_ne_top 1 b (by norm_num) hb1 hhitb
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
  have hTle : toppleTime 1 b ≤ (T : ℕ∞) := le_of_eq hT.symm
  have hTge : (T : ℕ∞) ≤ toppleTime 1 b := le_of_eq hT
  have hTlt : (T : ℕ∞) < toppleTime 1 a := lt_of_le_of_lt hTge hcon
  -- the corner of the side-`b` cube reaches `b` at time `T`
  have hbT : (b : ℤ) ≤ odoUnif 1 (2 * b) T (cornerPoint 1 b) := by
    have h := (toppleTime_le_iff 1 b (by norm_num) hb1 hhitb (T : ℕ∞)).mp hTle
    obtain ⟨n, hn, hn1, hnval⟩ := h
    have hnT : n ≤ T := ENat.natCast_le_natCast.mp hn
    have hmono' : odoUnif 1 (2 * b) n (cornerPoint 1 b)
        ≤ odoUnif 1 (2 * b) T (cornerPoint 1 b) :=
      odo_mono 1 (2 * b) (fun _ => 2) hnT _
    linarith
  -- the consistency clause at scale `b` at time `T`
  have hcons := hconsist T (le_of_lt hTlt)
  have hcorner : cornerPoint 1 b = (fun _ : Fin 1 => (b : ℤ)) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [cornerPoint]
    simp
  have hcornera : cornerPoint 1 a = (fun _ : Fin 1 => (a : ℤ)) := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [cornerPoint]
    simp
  rw [hcorner] at hbT
  rw [hcorner, hcornera] at hcons
  -- so the corner of the side-`a` cube exceeds `a` at time `T < τ_a`
  have haT : (a : ℤ) < odoUnif 1 (2 * a) T (fun _ : Fin 1 => (a : ℤ)) := by
    rw [← hcons]
    have : (a : ℤ) < (b : ℤ) := by
      have hne : a ≠ b := by
        intro heq
        rw [heq] at hcon
        exact absurd hcon (lt_irrefl _)
      exact_mod_cast (lt_of_le_of_ne hab hne)
    linarith
  -- contradicting `T < τ_a`
  have hiff := (toppleTime_le_iff 1 a (by norm_num) ha hhita (T : ℕ∞)).mpr
  have hle : toppleTime 1 a ≤ (T : ℕ∞) :=
    hiff ⟨T, le_rfl, by
      have h1 : (1 : ℕ∞) ≤ (T : ℕ∞) := by
        have h2 : (1 : ℕ∞) ≤ toppleTime 1 b := one_le_toppleTime 1 b
        exact le_trans h2 hTle
      exact ENat.natCast_le_natCast.mp h1, by
      rw [hcornera]; exact le_of_lt haT⟩
  exact absurd hle (not_le.mpr hTlt)
end DimRed
