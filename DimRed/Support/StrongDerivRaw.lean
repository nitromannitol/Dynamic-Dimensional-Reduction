/-
The second half of the strong-derivative route of
`scratch/case2-2026-09-24/lean-plan.md`: the raw forms of weak and strong facet
compatibility at a point of the positive orthant, obtained from the facet normal
form, and the estimates that consume them.
-/
import DimRed.Support.StrongDerivPure
import DimRed.Support.FacetNormal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- Weak facet compatibility at a raw point of the positive orthant, from the
clause at the facet normal form. -/
theorem weak_raw (d M t : ℕ) (ht : 1 ≤ t) (hW : RegWeak d M t)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1)
    (h : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1) :
    odoUnif d (2 * M) (t + 1) x = odoUnif d (2 * M) t x := by
  obtain ⟨i, j, hij, z, hz2, hzs, hi, hodo⟩ := facet_normal_form d M x hx k hk
  have h1 := (hodo t).1
  have h2 := (hodo t).2
  have h3 := (hodo (t + 1)).1
  have hlow : odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) + 1 := by
    rw [← h1, ← h2]; exact h
  have hW' := hW i j hij ht z hz2 hzs hlow
  rw [h3, h1]; exact hW'

/-- Strong facet compatibility at a raw point of the positive orthant, from the
clause at the facet normal form. -/
theorem strong_raw (d M t : ℕ) (hS : RegStrongFacet d M t)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) (h2 : ∃ l, 2 ≤ x l)
    (h : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1) :
    odoUnif d (2 * M) (t + 1) (x + unit k) = odoUnif d (2 * M) t (x + unit k) + 1 := by
  obtain ⟨i, j, hij, z, hz2, hzs, hi, hodo⟩ := facet_normal_form d M x hx k hk
  have h1 := (hodo t).1
  have h2' := (hodo t).2
  have h4 := (hodo (t + 1)).2
  have hlow : odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) + 1 := by
    rw [← h1, ← h2']; exact h
  have hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)) := by
    by_cases ht : (t : ℕ∞) < toppleTime (i + 1 + j) M
    · exact Or.inl ht
    · exact Or.inr ⟨hi h2, le_of_not_gt ht⟩
  have hS' := (hS i j hij z hz2 hzs hreg hlow).2
  rw [h4, h2']; exact hS'

/-- The facet case of the time-shifted first difference. -/
theorem odo_time_diff_one (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s)
    (s : ℕ) (hs : s + 2 ≤ T)
    (hIH : ∀ (k : Fin d) (x : Site d), inPos d M x →
      odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) s (x + unit k) ≤ x k)
    (k : Fin d) (x : Site d) (hx : inPos d M x)
    (hk1 : x k = 1) :
    odoUnif d (2 * M) (s + 2) x - odoUnif d (2 * M) (s + 1) (x + unit k) ≤ x k := by
  have hstep := odo_succ_sub_bounds d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x
  have hstep1 : 0 ≤ odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 2) x
      - odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x := by
    simpa [show s + 1 + 1 = s + 2 by omega] using hstep.1
  have hxk1 : (1 : ℤ) ≤ x k := by rw [hk1]
  have hfirst := odo_first_diff d M hd hM (s + 1) k x hxk1
  have hIH' := hIH k x hx
  rw [hk1] at hfirst hIH' ⊢
  by_cases hfire : odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 2) x
      = odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x + 1
  · have h1 : odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 2) x
        = odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x + 1 := hfire
    have h2 : odoUnif d (2 * M) (s + 1) x ≤ odoUnif d (2 * M) (s + 1) (x + unit k) := by
      by_contra hcon
      have heq : odoUnif d (2 * M) (s + 1) x
          = odoUnif d (2 * M) (s + 1) (x + unit k) + 1 := by omega
      have hW' := hW (s + 1) (by omega) (by omega)
      have hcontra := weak_raw d M (s + 1) (by omega) hW' x hx k hk1 heq
      have hcontra' : odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 2) x
          = odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x := by
        rw [show s + 1 + 1 = s + 2 by omega] at hcontra
        exact hcontra
      omega
    simp only [odoUnif] at h2 ⊢
    rw [h1]
    linarith
  · have hstay : odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 2) x
        = odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x := by
      have h := hstep1
      have h' : odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1 + 1) x
          - odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x ≤ 1 := hstep.2
      have e : s + 1 + 1 = s + 2 := by omega
      rw [e] at h h'
      omega
    simp only [odoUnif] at hfirst ⊢
    rw [hstay]
    linarith


/-- The time-shifted first difference `eq:time_difference`, `dimred.tex:1360-1372`. -/
theorem odo_time_diff (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s) :
    ∀ s, s + 1 ≤ T → ∀ (k : Fin d) (x : Site d), inPos d M x →
      odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) s (x + unit k) ≤ x k := by
  intro s
  induction s with
  | zero =>
    intro _ k x hx
    have h1 : odoUnif d (2 * M) 1 x = 1 := by
      have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have h := Frozen.pt_ind_lemma d (2 * M) (by omega) (fun _ => 2 * (d : ℤ))
        (fun _ _ => by positivity)
        (fun _ _ => by linarith) 0 x (inPos_inCube hx)
      simp only [nbrSum, odoUnif, odo] at h ⊢
      rw [h]
      have hz : (∑ i : Fin d, ((0 : ℤ) + 0)) = 0 := by simp
      rw [hz]
      have hdd : (2 * (d : ℤ) + 0) / (2 * (d : ℤ)) = 1 := by
        rw [add_zero]
        exact Int.ediv_self (by omega : (2 * (d : ℤ)) ≠ 0)
      rw [hdd]
    have h0 : odoUnif d (2 * M) 0 (x + unit k) = 0 := rfl
    rw [h1, h0]
    have := (hx k).1
    omega
  | succ n ih =>
    intro hs k x hx
    have ih' : ∀ (k : Fin d) (x : Site d), inPos d M x →
        odoUnif d (2 * M) (n + 1) x - odoUnif d (2 * M) n (x + unit k) ≤ x k :=
      fun k x hx => ih (by omega : n + 1 ≤ T) k x hx
    rcases lt_trichotomy (x k) 1 with hlt | heq | hgt
    · have := (hx k).1; omega
    · exact odo_time_diff_one d M T hd hM hW n hs ih' k x hx heq
    · by_cases htop : x k = (M : ℤ)
      · exact odo_time_diff_top d M hd hM (n + 1) k x htop
      · have hk2 : 2 ≤ x k := by omega
        have hkM : x k ≤ (M : ℤ) - 1 := by
          have h := (hx k).2
          omega
        exact odo_time_diff_mid d M T hd hM hW n hs ih' k x hx hk2 hkM
          (odo_time_diff_mid_nbr d M T hd hM hW n hs ih' k x hx hk2 hkM)





/-- The facet lag bound `eq:facet_lag`, `dimred.tex:1374-1379`. -/
theorem odo_facet_lag (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hS : ∀ s, s < T → RegStrongFacet d M s) (s : ℕ) (hs : s + 1 ≤ T)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) (h2 : ∃ l, 2 ≤ x l) :
    odoUnif d (2 * M) s x ≤ odoUnif d (2 * M) (s + 1) (x + unit k) := by
  have hxk1 : (1 : ℤ) ≤ x k := by rw [hk]
  have hfirst := odo_first_diff d M hd hM s k x hxk1
  by_cases heq : odoUnif d (2 * M) s x = odoUnif d (2 * M) s (x + unit k) + 1
  · have hstrong := strong_raw d M s (hS s (by omega)) x hx k hk h2 heq
    omega
  · have hmono : odoUnif d (2 * M) s (x + unit k) ≤ odoUnif d (2 * M) (s + 1) (x + unit k) :=
      odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (Nat.le_succ s) (x + unit k)
    rw [hk] at hfirst
    omega

/-- The strong derivative clause for a nonempty head, from the pure second
difference off the top coordinate. -/
theorem strong_deriv_pos_head (M i j t : ℕ) (_hM : 2 ≤ M) (hi : 1 ≤ i)
    (hpure : ∀ s, s ≤ t → ∀ (k : Fin (i + 1 + j)) (x : Site (i + 1 + j)),
      inPos (i + 1 + j) M x → (∃ l, x k < x l) →
      odoUnif (i + 1 + j) (2 * M) s x
        - odoUnif (i + 1 + j) (2 * M) s (x + unit k + unit k) ≤ 2 * x k)
    (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2 := by
  have hmid : facetPoint x 1 j (Fin.castAdd j (Fin.last i)) = 1 := facetPoint_mid x 1
  have hpos : inPos (i + 1 + j) M (facetPoint x 1 j) := hxs.1
  have hlt : facetPoint x 1 j (Fin.castAdd j (Fin.last i))
      < facetPoint x 1 j (Fin.castAdd j (Fin.castSucc ⟨0, hi⟩)) := by
    rw [hmid, facetPoint_head]
    have := hx2 ⟨0, hi⟩
    omega
  have hfar : facetPoint x 3 j = facetPoint x 1 j + unit (Fin.castAdd j (Fin.last i))
      + unit (Fin.castAdd j (Fin.last i)) := by
    rw [facetPoint_add_mid_point x 1]
    rw [show (1 : ℤ) + 1 = 2 by norm_num]
    rw [facetPoint_add_mid_point x 2]
    norm_num
  have h := hpure t le_rfl (Fin.castAdd j (Fin.last i)) (facetPoint x 1 j) hpos
    ⟨Fin.castAdd j (Fin.castSucc ⟨0, hi⟩), hlt⟩
  rw [hfar]
  rw [hmid] at h
  linarith

/-- The dissipating-boundary case of the mixed second difference: a coordinate
equal to `M` puts the far point off the cube. -/
theorem mixed_top (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s : ℕ) (k l : Fin d) (_hkl : k ≠ l)
    (x : Site d) (hx : inPos d M x) (hk : x k = (M : ℤ)) :
    odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) (s + 1) (x + unit k + unit l)
      ≤ x k + x l - 1 := by
  have hout : ¬ inCube d (2 * M) (x + unit k + unit l) := by
    intro hc
    have h := hc k
    rw [hiCoord_two_mul] at h
    have hk' : (x + unit k + unit l) k = x k + 1 + (if k = l then 1 else 0) := by
      rw [add_unit_apply, add_unit_apply]
      rw [if_pos rfl]
    rw [hk', hk] at h
    split_ifs at h <;> linarith [h.2]
  have hzero : odoUnif d (2 * M) (s + 1) (x + unit k + unit l) = 0 :=
    odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) _ hout
  have hle : odoUnif d (2 * M) (s + 1) x ≤ (M : ℤ) := by
    by_cases hx' : inCube d (2 * M) x
    · have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hc := odo_le_corner d M hd (2 * (d : ℤ)) (by positivity) (by linarith)
        (s + 1) x hx' k hk
      have hM' := odo_corner_le_M d M hd hM (s + 1)
      simp only [odoUnif] at hc hM' ⊢
      linarith
    · simp only [odoUnif, odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x hx']
      exact Int.natCast_nonneg M
  rw [hzero, hk]
  have := (hx l).1
  linarith

/-- The reflecting-boundary case of the mixed second difference: a coordinate
equal to `1` is handled by the facet lag bound and the time-shifted first
difference. -/
theorem mixed_reflect (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s) (hS : ∀ s, s < T → RegStrongFacet d M s)
    (s : ℕ) (hs : s + 1 ≤ T) (k l : Fin d) (hkl : k ≠ l) (x : Site d) (hx : inPos d M x)
    (hk1 : x k = 1) (hlM : x l ≤ (M : ℤ) - 1) :
    odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) (s + 1) (x + unit k + unit l)
      ≤ x k + x l - 1 := by
  have hpos : inPos d M (x + unit l) := by
    intro m
    have hm := hx m
    rw [add_unit_apply]
    by_cases hml : m = l
    · subst hml
      rw [if_pos rfl]
      constructor <;> omega
    · rw [if_neg hml, add_zero]; exact hm
  have h2 : ∃ m, 2 ≤ (x + unit l) m := ⟨l, by
    rw [add_unit_self]
    have := (hx l).1
    omega⟩
  have hk1' : (x + unit l) k = 1 := by
    rw [add_unit_apply]
    rw [if_neg hkl, add_zero, hk1]
  have hlag := odo_facet_lag d M T hd hM hS s (by omega) (x + unit l) hpos k hk1' h2
  have htd := odo_time_diff d M T hd hM hW s (by omega) l x hx
  have hcomm : x + unit k + unit l = (x + unit l) + unit k := by abel
  rw [hcomm]
  linarith

/-- A point of the positive orthant whose two named coordinates are at most
`M - 1` stays in the cube after a step in both directions. -/
theorem mixed_hxw (d M : ℕ) (k l : Fin d) (hkl : k ≠ l) (x : Site d) (hx : inPos d M x)
    (hkM : x k ≤ (M : ℤ) - 1) (hlM : x l ≤ (M : ℤ) - 1) :
    inCube d (2 * M) (x + (unit k + unit l)) := by
  intro i
  rw [loCoord_two_mul, hiCoord_two_mul]
  have h := hx i
  simp only [Pi.add_apply, unit, Pi.single_apply]
  by_cases hik : i = k
  · subst hik
    simp only [if_neg hkl, add_zero]
    omega
  · simp only [if_neg hik]
    by_cases hil : i = l
    · subst hil
      omega
    · simp only [if_neg hil, add_zero]
      omega

/-- The mixed second difference `eq:mixed_difference`, `dimred.tex:1381-1394`. -/
theorem odo_mixed_diff (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s) (hS : ∀ s, s < T → RegStrongFacet d M s) :
    ∀ s, s ≤ T → ∀ (k l : Fin d), k ≠ l → ∀ x : Site d, inPos d M x →
      odoUnif d (2 * M) s x - odoUnif d (2 * M) s (x + unit k + unit l) ≤ x k + x l - 1 := by
  intro s
  induction s with
  | zero =>
    intro _ k l _ x hx
    have h1 : odoUnif d (2 * M) 0 x = 0 := rfl
    have h2 : odoUnif d (2 * M) 0 (x + unit k + unit l) = 0 := rfl
    rw [h1, h2]
    have hk := (hx k).1
    have hl := (hx l).1
    omega
  | succ n ih =>
    intro hs k l hkl x hx
    by_cases hkM : x k = (M : ℤ)
    · exact mixed_top d M hd hM n k l hkl x hx hkM
    by_cases hlM : x l = (M : ℤ)
    · have hkl' : l ≠ k := Ne.symm hkl
      have hcomm : x + unit k + unit l = x + unit l + unit k := by abel
      rw [hcomm]
      have h := mixed_top d M hd hM n l k hkl' x hx hlM
      linarith
    by_cases hk1 : x k = 1
    · have hlM' : x l ≤ (M : ℤ) - 1 := by
        have h := (hx l).2
        omega
      exact mixed_reflect d M T hd hM hW hS n (by omega) k l hkl x hx hk1 hlM'
    by_cases hl1 : x l = 1
    · have hkl' : l ≠ k := Ne.symm hkl
      have hcomm : x + unit k + unit l = x + unit l + unit k := by abel
      rw [hcomm]
      have hkM' : x k ≤ (M : ℤ) - 1 := by
        have h := (hx k).2
        omega
      have h := mixed_reflect d M T hd hM hW hS n (by omega) l k hkl' x hx hl1 hkM'
      linarith
    have hk2 : 2 ≤ x k := by have := (hx k).1; omega
    have hl2 : 2 ≤ x l := by have := (hx l).1; omega
    have hkM' : x k ≤ (M : ℤ) - 1 := by have := (hx k).2; omega
    have hlM' : x l ≤ (M : ℤ) - 1 := by have := (hx l).2; omega
    have hx' : inCube d (2 * M) x := inPos_inCube hx
    have hxw : inCube d (2 * M) (x + (unit k + unit l)) := mixed_hxw d M k l hkl x hx hkM' hlM'
    have hG : nbrSum (fun y : Site d => y k + y l - 1) x = 2 * (d : ℤ) * (x k + x l - 1) := by
      have hk := nbrSum_affine (fun m : Fin d => if m = k then (1:ℤ) else 0) 0 x
      have hl := nbrSum_affine (fun m : Fin d => if m = l then (1:ℤ) else 0) 0 x
      have h1 : (fun y : Site d => ∑ m : Fin d, (if m = k then (1:ℤ) else 0) * y m + 0)
          = fun y => y k := by
        funext y
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ k) hb
      have h2 : (fun y : Site d => ∑ m : Fin d, (if m = l then (1:ℤ) else 0) * y m + 0)
          = fun y => y l := by
        funext y
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ l) hb
      rw [h1] at hk
      rw [h2] at hl
      have h3 : (∑ m : Fin d, (if m = k then (1:ℤ) else 0) * x m + 0) = x k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ k) hb
      have h4 : (∑ m : Fin d, (if m = l then (1:ℤ) else 0) * x m + 0) = x l := by
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ l) hb
      rw [h3] at hk
      rw [h4] at hl
      have hsum : nbrSum (fun y : Site d => y k + y l - 1) x
          = nbrSum (fun y : Site d => y k) x + nbrSum (fun y : Site d => y l) x
            - nbrSum (fun _ : Site d => (1:ℤ)) x := by
        simp only [nbrSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
      have hone : nbrSum (fun _ : Site d => (1:ℤ)) x = 2 * (d : ℤ) := by
        simp only [nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hsum, hk, hl, hone]
      ring
    have hfloor := floor_step d M hd n n x (unit k + unit l) hx' hxw (x k + x l - 1) ?_
    · have hcomm : x + unit k + unit l = x + (unit k + unit l) := by abel
      rw [hcomm]
      simpa [Nat.add_assoc] using hfloor
    · refine nbrSum_sub_le_of_terms (odoUnif d (2 * M) n) (odoUnif d (2 * M) n)
        x (unit k + unit l) (fun y => y k + y l - 1) hG ?_ ?_
      · intro m
        rcases inPos_add_unit_or hx m with h | h
        · have hc : x + unit m + (unit k + unit l) = (x + unit m) + unit k + unit l := by abel
          rw [hc]
          exact ih (by omega) k l hkl (x + unit m) h
        · have hmk : m ≠ k := by rintro rfl; omega
          have hml : m ≠ l := by rintro rfl; omega
          have hterm := term_outside d M n n (x + unit m) (unit k + unit l)
            (not_inCube_add_unit_of_eq m h)
          have hvk : (x + unit m) k = x k := add_unit_other d x m k (Ne.symm hmk)
          have hvl : (x + unit m) l = x l := add_unit_other d x m l (Ne.symm hml)
          rw [hvk, hvl]
          have h1 := (hx k).1
          have h2 := (hx l).1
          linarith [hterm]
      · intro m
        rcases inPos_sub_unit_or hx m with h | h
        · have hc : x - unit m + (unit k + unit l) = (x - unit m) + unit k + unit l := by abel
          rw [hc]
          exact ih (by omega) k l hkl (x - unit m) h
        · have hmk : m ≠ k := by rintro rfl; omega
          have hml : m ≠ l := by rintro rfl; omega
          have hwl : (unit k + unit l : Site d) m = 0 := by
            simp only [Pi.add_apply, unit_apply_ne hmk, unit_apply_ne hml, add_zero]
          have hterm := term_reflect d M n n x (unit k + unit l) m h hwl
          have hvk : (x - unit m) k = x k := sub_unit_other d x m k (Ne.symm hmk)
          have hvl : (x - unit m) l = x l := sub_unit_other d x m l (Ne.symm hml)
          rw [hterm, hvk, hvl]
          have hc : x + (unit k + unit l) = x + unit k + unit l := by abel
          rw [hc]
          exact ih (by omega) k l hkl x hx

end DimRed
