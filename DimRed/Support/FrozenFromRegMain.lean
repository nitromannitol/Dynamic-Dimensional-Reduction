import DimRed.Support.FrozenFromRegOdd
import DimRed.Support.SandpileFromOdo

/-!
# The main results for every side `N` from the joint induction

The joint induction `reg_all` proves the five regularity clauses and dimensional reduction on the
even cubes `C_{2M}^{(d)}` with `M ≥ 2`.  The main statements of Theorem 1.1 and of its corollary
are stated for every `N ≥ 1` and `M = ⌈N / 2⌉`.  Three things bridge the gap.

* For odd `N`, the odometer on `C_N^{(d)}` agrees with the one on `C_{2M}^{(d)}` on the region
  `x ≥ 1` (`odoUnif_odd_eq_even`), which needs only weak facet compatibility.
* For `M = 1`, i.e. `N ∈ {1, 2}`, the statement is a computation at the all-ones point.
* The terminal identity `v_∞(x, 2) = v_∞(x, 1)` follows from strong facet compatibility at every
  time: the two odometers are interleaved, `v_t(x, 2) ≤ v_t(x, 1) ≤ v_{t+1}(x, 2)`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

open LatticeProb

namespace DimRed

theorem sideHalf_cases (N : ℕ) : N = 2 * sideHalf N ∨ N + 1 = 2 * sideHalf N := by
  simp only [sideHalf]
  omega

/-- The terminal odometer depends only on the odometer at every time. -/
theorem odoInfUnif_congr (D D' N N' : ℕ) (y : Site D) (y' : Site D')
    (h : ∀ t, odoUnif D N t y = odoUnif D' N' t y') :
    odoInfUnif D N y = odoInfUnif D' N' y' := by
  unfold odoInfUnif odoInf
  refine iSup_congr fun t => ?_
  have := h t
  simp only [odoUnif] at this
  rw [this]

/-- Dropping to the even cube of side `2 ⌈N / 2⌉`: on the region `x ≥ 1` the odometer on the
cube of side `N` is the odometer on the even cube of side `2 ⌈N / 2⌉`. -/
theorem odoUnif_scale_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ sideHalf N) (t : ℕ) (x : Site d) (hx : ∀ i, 1 ≤ x i) :
    odoUnif d N t x = odoUnif d (2 * sideHalf N) t x := by
  rcases sideHalf_cases N with h | h
  · rw [← h]
  · exact odoUnif_odd_eq_even d (sideHalf N) hd hM
      (fun t => (hreg d _ t hd hM).1.2.1) N h t x hx

theorem snoc_pos_of_pos {d : ℕ} (x : Site d) (c : ℤ) (hc : 1 ≤ c) (hx : ∀ i, 1 ≤ x i) :
    ∀ k, 1 ≤ (Fin.snoc x c : Site (d + 1)) k := by
  intro k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simpa using hc
  · simpa using hx i

/-- Theorem 1.1(i), first display, for every `N ≥ 1`. -/
theorem dimensional_reduction_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x := by
  have hM1 : 1 ≤ sideHalf N := by simp only [sideHalf]; omega
  rcases Nat.lt_or_ge (sideHalf N) 2 with hlt | hM
  · have hN' : N = 1 ∨ N = 2 := by simp only [sideHalf] at hlt; omega
    have hx1 : x = fun _ => 1 := funext fun i => by
      have := hx.1 i
      omega
    have hs : (Fin.snoc x 1 : Site (d + 1)) = fun _ => 1 := by
      funext k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp
      · simp [hx1]
    rw [hs, hx1, odoUnif_ones_eq_one (d + 1) N (by omega) hN' t ht,
      odoUnif_ones_eq_one d N hd hN' t ht]
  · obtain ⟨M, hMdef⟩ : ∃ M, sideHalf N = M := ⟨_, rfl⟩
    rw [hMdef] at hx hM
    have hDR := (hreg (d + 1) M t (by omega) hM).2 d hd rfl x hx
    rcases sideHalf_cases N with h | h
    · rw [hMdef] at h
      subst h
      exact hDR
    · rw [hMdef] at h
      have e1 := odoUnif_odd_eq_even (d + 1) M (by omega) hM
        (fun t => (hreg (d + 1) M t (by omega) hM).1.2.1) N h t (Fin.snoc x 1)
        (snoc_pos_of_pos x 1 le_rfl (fun i => (hx.1 i).1))
      have e2 := odoUnif_odd_eq_even d M hd hM
        (fun t => (hreg d M t hd hM).1.2.1) N h t x (fun i => (hx.1 i).1)
      rw [e1, e2]
      exact hDR

/-- Dimensional reduction at every time, including `t = 0`. -/
theorem dimensional_reduction_all_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (t : ℕ) :
    odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [odoUnif, odo]
  · exact dimensional_reduction_of_reg hreg N d hN hd t ht x hx

/-- Theorem 1.1(ii) for every `N ≥ 1`. -/
theorem self_similarity_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (_hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    odoUnif d N t x = odoUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  have hj1 : 1 ≤ j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst hj0
    have h1 := hxgt ⟨0, by omega⟩
    have h2 := (hx.1 ⟨0, by omega⟩).2
    omega
  have hM : 2 ≤ sideHalf N := by omega
  rw [odoUnif_scale_of_reg hreg N d (by omega) hM t x (fun i => (hx.1 i).1)]
  exact (hreg d (sideHalf N) t (by omega) hM).1.1 j hj1 (le_of_lt hj) ht x hx hxgt

/-- The two odometers at `(x, 1)` and `(x, 2)` interleave, so their terminal values agree. -/
theorem odoInfUnif_snoc_two_eq_one (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hS : ∀ t, RegStrongFacet (d + 1) M t) (x : Site d) (hx : inSimplex d M x)
    (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) (2 * M) (Fin.snoc x 2) = odoInfUnif (d + 1) (2 * M) (Fin.snoc x 1) := by
  have hy : inPos (d + 1) M (Fin.snoc x 1) := (inSimplex_snoc_one_local x hx (by omega)).1
  have hlast : (Fin.snoc x 1 : Site (d + 1)) (Fin.last d) = 1 := by simp
  have hpt : (Fin.snoc x 2 : Site (d + 1)) = Fin.snoc x 1 + unit (Fin.last d) := by
    have h := fin_snoc_add_last x 1
    norm_num at h
    exact h
  have hdZ : (1 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 1 ≤ d + 1)
  have hle : ∀ t, odoUnif (d + 1) (2 * M) t (Fin.snoc x 2)
      ≤ odoUnif (d + 1) (2 * M) t (Fin.snoc x 1) := by
    intro t
    rw [hpt]
    exact odo_axis_refl (d + 1) M (by omega) (2 * ((d + 1 : ℕ) : ℤ)) (by positivity)
      (by linarith) t (Fin.snoc x 1) (Fin.last d) (by omega)
  have hfd : ∀ t, odoUnif (d + 1) (2 * M) t (Fin.snoc x 1)
      - odoUnif (d + 1) (2 * M) t (Fin.snoc x 1 + unit (Fin.last d)) ≤ 1 := by
    intro t
    have h := odo_first_diff (d + 1) M (by omega) (by omega) t (Fin.last d) (Fin.snoc x 1)
      (by omega)
    rw [hlast] at h
    exact h
  have hx2' : ∃ l, 2 ≤ (Fin.snoc x 1 : Site (d + 1)) l := by
    refine ⟨Fin.castSucc ⟨0, by omega⟩, ?_⟩
    rw [Fin.snoc_castSucc]
    exact hx2 _
  have hge : ∀ t, odoUnif (d + 1) (2 * M) t (Fin.snoc x 1)
      ≤ odoUnif (d + 1) (2 * M) (t + 1) (Fin.snoc x 2) := by
    intro t
    rw [hpt]
    have hmono : odoUnif (d + 1) (2 * M) t (Fin.snoc x 1 + unit (Fin.last d))
        ≤ odoUnif (d + 1) (2 * M) (t + 1) (Fin.snoc x 1 + unit (Fin.last d)) :=
      odo_mono (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) (Nat.le_succ t) _
    have hle' := hle t
    rw [hpt] at hle'
    by_cases hgap : odoUnif (d + 1) (2 * M) t (Fin.snoc x 1)
        = odoUnif (d + 1) (2 * M) t (Fin.snoc x 1 + unit (Fin.last d)) + 1
    · have h := strong_raw (d + 1) M t (hS t) (Fin.snoc x 1) hy (Fin.last d) hlast hx2' hgap
      omega
    · have := hfd t
      omega
  have hiSup : ∀ (D N : ℕ) (y : Site D), odoInfUnif D N y
      = ⨆ t : ℕ, ((odoUnif D N t y).toNat : ℕ∞) := fun _ _ _ => rfl
  rw [hiSup, hiSup]
  apply le_antisymm
  · refine iSup_le fun t => ?_
    exact le_trans (Nat.cast_le.2 (Int.toNat_le_toNat (hle t)))
      (le_iSup (fun t : ℕ => ((odoUnif (d + 1) (2 * M) t (Fin.snoc x 1)).toNat : ℕ∞)) t)
  · refine iSup_le fun t => ?_
    exact le_trans (Nat.cast_le.2 (Int.toNat_le_toNat (hge t)))
      (le_iSup (fun t : ℕ => ((odoUnif (d + 1) (2 * M) t (Fin.snoc x 2)).toNat : ℕ∞)) (t + 1))

/-- Theorem 1.1(i), second display, for every `N ≥ 1`. -/
theorem terminal_dimensional_reduction_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (_hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) N (Fin.snoc x 2) = odoInfUnif d N x := by
  have hM : 2 ≤ sideHalf N := by
    have h1 := (hx.1 ⟨0, by omega⟩).2
    have h2 := hx2 ⟨0, by omega⟩
    omega
  have hxpos : ∀ i, 1 ≤ x i := fun i => (hx.1 i).1
  calc odoInfUnif (d + 1) N (Fin.snoc x 2)
      = odoInfUnif (d + 1) (2 * sideHalf N) (Fin.snoc x 2) :=
        odoInfUnif_congr _ _ _ _ _ _ (fun t =>
          odoUnif_scale_of_reg hreg N (d + 1) (by omega) hM t _
            (snoc_pos_of_pos x 2 (by norm_num) hxpos))
    _ = odoInfUnif (d + 1) (2 * sideHalf N) (Fin.snoc x 1) :=
        odoInfUnif_snoc_two_eq_one d (sideHalf N) hd hM
          (fun t => (hreg (d + 1) _ t (by omega) hM).1.2.2.2.1) x hx hx2
    _ = odoInfUnif d (2 * sideHalf N) x :=
        odoInfUnif_congr _ _ _ _ _ _ (fun t =>
          (hreg (d + 1) _ t (by omega) hM).2 d hd rfl x hx)
    _ = odoInfUnif d N x :=
        odoInfUnif_congr _ _ _ _ _ _ (fun t =>
          (odoUnif_scale_of_reg hreg N d hd hM t x hxpos).symm)

/-- Corollary 1.1(i) for every `N ≥ 1`. -/
theorem sandpile_dimensional_reduction_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    sandpInfUnif (d + 1) N (Fin.snoc x 1) = sandpInfUnif d N x + 2 :=
  sandp_dimred_of_odo N d hN hd x hx hx2
    (fun y hy => odoInfUnif_congr _ _ _ _ _ _
      (dimensional_reduction_all_of_reg hreg N d hN hd y hy))
    (fun y hy hy2 => terminal_dimensional_reduction_of_reg hreg N d hN hd y hy hy2)

/-- Corollary 1.1(ii) for every `N ≥ 1`. -/
theorem sandpile_self_similarity_of_reg
    (hreg : ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t)
    (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    sandpUnif d N t x = sandpUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) :=
  sandp_selfsim_of_odo N d hN hd j t hj x hx hxgt
    (fun y hy hygt => self_similarity_of_reg hreg N d hN hd j hj t ht y hy hygt)

end DimRed
