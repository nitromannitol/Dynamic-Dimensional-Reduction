import DimRed.Support.DerivBound

/-!
The toppling time and its corner reduction, including the strict pre-toppling
bound used at the dissipating boundary in Section 4 of the paper,
`dimred-corrected-arxiv.tex`.
-/
namespace DimRed

open LatticeProb

theorem innerBoundary_mem_cube {d N : ℕ} {x : Site d}
    (hx : x ∈ innerBoundary d N) : inCube d N x := by
  classical
  simp only [innerBoundary, Finset.mem_filter] at hx
  have h := Finset.mem_Icc.mp hx.1
  intro i
  exact ⟨h.1 i, h.2 i⟩

theorem innerBoundary_coord (d M : ℕ) {x : Site d} (hx : x ∈ innerBoundary d (2 * M)) :
    ∃ i : Fin d, x i = (M : ℤ) ∨ x i = 1 - (M : ℤ) := by
  classical
  have hcube : inCube d (2 * M) x := innerBoundary_mem_cube hx
  simp only [innerBoundary, Finset.mem_filter] at hx
  rcases hx.2 with ⟨i, hplus | hminus⟩
  · by_cases hi : x i = (M : ℤ)
    · exact ⟨i, Or.inl hi⟩
    · refine ⟨i, Or.inl ?_⟩
      by_contra hne
      apply hplus
      intro k
      have hk := hcube k
      rw [loCoord_two_mul, hiCoord_two_mul] at hk ⊢
      by_cases hki : k = i
      · subst k
        rw [add_unit_self]
        omega
      · rw [add_unit_other _ _ _ _ hki]
        exact hk
  · by_cases hi : x i = 1 - (M : ℤ)
    · exact ⟨i, Or.inr hi⟩
    · refine ⟨i, Or.inr ?_⟩
      by_contra hne
      apply hminus
      intro k
      have hk := hcube k
      rw [loCoord_two_mul, hiCoord_two_mul] at hk ⊢
      by_cases hki : k = i
      · subst k
        rw [sub_unit_self]
        omega
      · rw [sub_unit_other _ _ _ _ hki]
        exact hk

theorem cornerPoint_mem_innerBoundary (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    cornerPoint d M ∈ innerBoundary d (2 * M) := by
  classical
  have hdpos : 0 < d := by omega
  let i : Fin d := ⟨0, hdpos⟩
  have hcube : inCube d (2 * M) (cornerPoint d M) := by
    intro k
    rw [loCoord_two_mul, hiCoord_two_mul, cornerPoint]
    split <;> omega
  have hout : ¬ inCube d (2 * M) (cornerPoint d M + unit i) := by
    intro h
    have hi := h i
    rw [loCoord_two_mul, hiCoord_two_mul, add_unit_self] at hi
    simp [cornerPoint, i] at hi
  have hmem : cornerPoint d M ∈ cube d (2 * M) := by
    rw [cube, Finset.mem_Icc]
    exact ⟨fun k => (hcube k).1, fun k => (hcube k).2⟩
  simpa only [innerBoundary, Finset.mem_filter] using (show
    cornerPoint d M ∈ cube d (2 * M) ∧
      ∃ i : Fin d, ¬ inCube d (2 * M) (cornerPoint d M + unit i) ∨
        ¬ inCube d (2 * M) (cornerPoint d M - unit i) from
    ⟨hmem, ⟨i, Or.inl hout⟩⟩)

theorem odo_innerBoundary_le_corner (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (t : ℕ)
    {x : Site d} (hx : x ∈ innerBoundary d (2 * M)) :
    odoUnif d (2 * M) t x ≤ odoUnif d (2 * M) t (cornerPoint d M) := by
  have hcube := innerBoundary_mem_cube hx
  obtain ⟨i, hi | hi⟩ := innerBoundary_coord d M hx
  · exact odo_le_corner d M hd (2 * (d : ℤ)) (by positivity) (by omega) t x hcube i hi
  · let y : Site d := fun k => if k = i then 1 - x i else x k
    have hMz : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    have hy : inCube d (2 * M) y := by
      intro k
      have hk := hcube k
      rw [loCoord_two_mul, hiCoord_two_mul] at hk ⊢
      by_cases hki : k = i
      · subst k
        simp [y, hi]
        omega
      · simp [y, hki]
        omega
    have hyi : y i = (M : ℤ) := by simp [y, hi]
    have hsym := odo_reflect_coord d M (2 * (d : ℤ)) t x i
    have hydef : y = fun k => if k = i then 1 - x i else x k := rfl
    rw [← hydef] at hsym
    change odo d (2 * M) (fun _ => 2 * (d : ℤ)) t x ≤
      odo d (2 * M) (fun _ => 2 * (d : ℤ)) t (cornerPoint d M)
    rw [← hsym]
    exact odo_le_corner d M hd (2 * (d : ℤ)) (by positivity) (by omega) t y hy i hyi

theorem sInf_nat_image_eq (s : Set ℕ) (hs : s.Nonempty) :
    sInf ((fun n : ℕ => (n : ℕ∞)) '' s) = ((show ℕ from sInf s) : ℕ∞) := by
  apply le_antisymm
  · exact sInf_le ⟨(show ℕ from sInf s), Nat.sInf_mem hs, rfl⟩
  · refine le_sInf ?_
    rintro _ ⟨n, hn, rfl⟩
    change ((sInf s : ℕ) : ℕ∞) ≤ (n : ℕ∞)
    exact_mod_cast Nat.sInf_le hn

theorem sInf_nat_image_le_iff (s : Set ℕ) (hs : s.Nonempty) (m : ℕ∞) :
    m ≥ sInf ((fun n : ℕ => (n : ℕ∞)) '' s) ↔
      ∃ n : ℕ, (n : ℕ∞) ≤ m ∧ n ∈ s := by
  rw [sInf_nat_image_eq s hs]
  constructor
  · intro hm
    exact ⟨(show ℕ from sInf s), by exact_mod_cast hm, Nat.sInf_mem hs⟩
  · rintro ⟨n, hnm, hn⟩
    have hnat : sInf s ≤ n := Nat.sInf_le hn
    have hcast : ((sInf s : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hnat
    exact le_trans hcast hnm

theorem toppleTime_eq_corner (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j) :
    toppleTime d j = sInf ((fun n : ℕ => (n : ℕ∞)) ''
      {n : ℕ | 1 ≤ n ∧
        (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)}) := by
  have hset : {n : ℕ | 1 ≤ n ∧
      ∃ x ∈ innerBoundary d (2 * j),
        (j : ℤ) ≤ odoUnif d (2 * j) n x} =
      {n : ℕ | 1 ≤ n ∧
        (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)} := by
    ext n
    constructor
    · rintro ⟨hn, x, hx, hxn⟩
      exact ⟨hn, hxn.trans (odo_innerBoundary_le_corner d j hd hj n hx)⟩
    · rintro ⟨hn, hcorner⟩
      exact ⟨hn, cornerPoint d j, cornerPoint_mem_innerBoundary d j hd hj, hcorner⟩
  rw [toppleTime, hset]

theorem toppleTime_le_iff (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hhit : ∃ n : ℕ, 1 ≤ n ∧
      (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)) (m : ℕ∞) :
    m ≥ toppleTime d j ↔
      ∃ n : ℕ, (n : ℕ∞) ≤ m ∧ 1 ≤ n ∧
        (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j) := by
  have hs : {n : ℕ | 1 ≤ n ∧
      (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)}.Nonempty := by
    rcases hhit with ⟨n, hn, hval⟩
    exact ⟨n, hn, hval⟩
  rw [toppleTime_eq_corner d j hd hj]
  simpa only [Set.mem_setOf_eq] using sInf_nat_image_le_iff _ hs m

theorem one_le_toppleTime (d j : ℕ) : 1 ≤ toppleTime d j := by
  refine le_sInf ?_
  rintro _ ⟨n, hn, rfl⟩
  change (1 : ℕ∞) ≤ (n : ℕ∞)
  exact_mod_cast hn.1

theorem toppleTime_ne_top (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hhit : ∃ n : ℕ, 1 ≤ n ∧
      (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)) :
    toppleTime d j ≠ ⊤ := by
  rcases hhit with ⟨n, hn, hval⟩
  have hle := (toppleTime_le_iff d j hd hj ⟨n, hn, hval⟩ (n : ℕ∞)).2
    ⟨n, le_rfl, hn, hval⟩
  intro htop
  rw [htop] at hle
  simp at hle

theorem odo_corner_lt_of_lt_toppleTime (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (t : ℕ)
    (ht : (t : ℕ∞) < toppleTime d M) (htpos : 1 ≤ t) :
    odoUnif d (2 * M) t (cornerPoint d M) ≤ (M : ℤ) - 1 := by
  by_contra hbound
  have hval : (M : ℤ) ≤ odoUnif d (2 * M) t (cornerPoint d M) := by omega
  have hle : toppleTime d M ≤ (t : ℕ∞) := by
    unfold toppleTime
    refine sInf_le ?_
    refine ⟨t, ⟨htpos, cornerPoint d M, cornerPoint_mem_innerBoundary d M hd hM, hval⟩, rfl⟩
  exact (not_lt_of_ge hle) ht

theorem toppleTime_mono (d j j' : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j) (hjj' : j ≤ j')
    (hcomp : ∀ n : ℕ, 1 ≤ n →
      (j' : ℤ) ≤ odoUnif d (2 * j') n (cornerPoint d j') →
      (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)) :
    toppleTime d j ≤ toppleTime d j' := by
  have hj' : 1 ≤ j' := le_trans hj hjj'
  let s : Set ℕ := {n : ℕ | 1 ≤ n ∧
    (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)}
  let s' : Set ℕ := {n : ℕ | 1 ≤ n ∧
    (j' : ℤ) ≤ odoUnif d (2 * j') n (cornerPoint d j')}
  by_cases hne : s'.Nonempty
  · have hmin : sInf s' ∈ s' := Nat.sInf_mem hne
    have hmin' : sInf s' ∈ s := by
      exact ⟨hmin.1, hcomp (sInf s') hmin.1 hmin.2⟩
    rw [toppleTime_eq_corner d j hd hj, toppleTime_eq_corner d j' hd hj']
    calc
      sInf ((fun n : ℕ => (n : ℕ∞)) '' s) ≤ ((sInf s' : ℕ) : ℕ∞) :=
        sInf_le ⟨sInf s', hmin', rfl⟩
      _ = sInf ((fun n : ℕ => (n : ℕ∞)) '' s') :=
        (sInf_nat_image_eq s' hne).symm
  · have hempty : s' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [toppleTime_eq_corner d j hd hj, toppleTime_eq_corner d j' hd hj']
    change sInf ((fun n : ℕ => (n : ℕ∞)) '' s) ≤
      sInf ((fun n : ℕ => (n : ℕ∞)) '' s')
    rw [hempty]
    simp

/-- The topple time is at least one when the boundary is reached. -/
theorem one_le_toppleTime_of_reached {d j : ℕ} (hd : 1 ≤ d) (hj : 1 ≤ j)
    (h : ∃ n : ℕ, 1 ≤ n ∧ (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j)) :
    (1 : ℕ∞) ≤ toppleTime d j := by
  obtain ⟨n, hn1, hn⟩ := h
  refine le_csInf ?_ ?_
  · exact ⟨(n : ℕ∞), n, ⟨hn1, cornerPoint d j, cornerPoint_mem_innerBoundary d j hd hj, hn⟩, rfl⟩
  · rintro m ⟨k, ⟨hk1, _⟩, rfl⟩
    exact Nat.cast_le.mpr hk1

end DimRed
