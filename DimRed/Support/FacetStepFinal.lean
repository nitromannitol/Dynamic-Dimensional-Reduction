import DimRed.Support.StrongRawLe
import DimRed.Support.FacetLapUncond
import DimRed.Support.FacetNbr
import DimRed.Support.NbrSumSelfSim
import DimRed.Support.DimRedCritical
import DimRed.Support.OneStep
import DimRed.Support.WeakStep

/-!
# The strong facet step of the joint induction

`facet_step_of_earlier` is the `hfacet_step` input of `reg_induction`.

Suppose `v_t(x, 1, 1_j) = v_t(x, 2, 1_j) + 1`.  Strong facet compatibility at
`t - 1` and the first-difference bound give the picture one step back: the two
points had the same value at `t - 1`, the first toppled from `t - 1` to `t` and
the second did not (`facet_prev`).

* The second point topples at `t` (`facet_mid_topples`): its Laplacian at `t`
  dominates the Laplacian of the first point at `t - 1`, which is nonnegative
  because that point toppled.  The comparison is neighbour by neighbour
  (`nbr_pair_le`, `mid_pair_le`, `lap_le_of_prev`), each term from strong facet
  compatibility at `t - 1` (`strong_raw_le`), the first-difference bound, the
  reflection and swap symmetries, and the two-step bound `hderiv` for the mid
  pair.  This is the paper's comparison of `eq:laplace_11`-`eq:laplace_13` with
  `eq:laplace_21`-`eq:laplace_23`, carried out termwise under the gap
  hypothesis; a head neighbour whose coordinate drops to one is handled by the
  swap symmetry, the first-difference bound and the toppling of the first point
  at `t - 1`, not by the paper's axis comparison (see `ledger/decisions.md`, D1).
* The first point does not topple at `t`.  With an empty head its Laplacian is
  `-(j+1)` (`odo_succ_facetPoint_zero_of`).  With a nonempty head, once `t - 1`
  has reached `τ_{M-1}`, strong topple control at `t - 1` freezes it, since it
  toppled at `t - 1` (`facet_head_stays_late`).  Before that time the gap cannot
  occur (`facet_no_gap_early`): dimensional reduction at `t` takes the facet pair
  to `(x, 1)`, `(x, 2)` in dimension `i + 1`, where the reflecting boundary
  identity `eq:reflecting_boundaries` holds at `t`.  The self-similarity input of
  that identity at the point `(x, 2)` is obtained from time `t - 1` by one
  toppling step (`selfsim_step_two`), so self-similarity at `(d, M, t)` itself,
  which the joint induction proves after this step, is not used.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

/-- The odometer is unchanged by the reflection in a coordinate equal to one. -/
theorem odoUnif_sub_unit_of_one {d : ℕ} (M s : ℕ) (u : Site d) (k : Fin d) (hu : u k = 1) :
    odoUnif d (2 * M) s (u - unit k) = odoUnif d (2 * M) s u := by
  have h := odo_reflect_coord d M (2 * (d : ℤ)) s (u - unit k) k
  rw [reflect_sub_of_one u k hu] at h
  simp only [odoUnif]
  exact h.symm

/-- The odometer is unchanged by the swap of two equal coordinates. -/
theorem odoUnif_add_unit_swap {d : ℕ} (M s : ℕ) (z : Site d) (k m : Fin d) (hkm : k ≠ m)
    (he : z k = z m) :
    odoUnif d (2 * M) s (z + unit m) = odoUnif d (2 * M) s (z + unit k) := by
  have h := odo_swap_coord d M (2 * (d : ℤ)) s (z + unit m) k m
  rw [swap_add_eq_add z k m hkm he] at h
  simp only [odoUnif]
  exact h.symm

private theorem odoUnif_fun_eq {d : ℕ} (N t : ℕ) :
    odoUnif d N t = odo d N (fun _ => 2 * (d : ℤ)) t := rfl

/-- A site which toppled from `t - 1` to `t` had a nonnegative Laplacian at `t - 1`. -/
theorem lap_nonneg_of_topple {d : ℕ} (M t : ℕ) (ht : 1 ≤ t) (p : Site d)
    (htop : odoUnif d (2 * M) t p = odoUnif d (2 * M) (t - 1) p + 1) :
    0 ≤ lap (odoUnif d (2 * M) (t - 1)) p := by
  by_cases hp : inCube d (2 * M) p
  · have h := odo_succ_eq d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1) p hp
    rw [show t - 1 + 1 = t by omega] at h
    simp only [odoUnif] at htop
    by_contra hneg
    have hlt : ¬ (2 * (d : ℤ) ≤ sandp d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1) p) := by
      simp only [sandp]
      rw [odoUnif_fun_eq] at hneg
      omega
    rw [if_neg hlt] at h
    omega
  · have h1 := odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) t p hp
    have h2 := odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1) p hp
    simp only [odoUnif] at htop
    omega

/-- A site of the cube with a nonnegative Laplacian at `t` topples from `t` to `t + 1`. -/
theorem topple_of_lap_nonneg {d : ℕ} (M t : ℕ) (p : Site d) (hp : inCube d (2 * M) p)
    (hlap : 0 ≤ lap (odoUnif d (2 * M) t) p) :
    odoUnif d (2 * M) (t + 1) p = odoUnif d (2 * M) t p + 1 := by
  have h := odo_succ_eq d (2 * M) (fun _ => 2 * (d : ℤ)) t p hp
  have hle : 2 * (d : ℤ) ≤ sandp d (2 * M) (fun _ => 2 * (d : ℤ)) t p := by
    simp only [sandp]
    rw [odoUnif_fun_eq] at hlap
    omega
  rw [if_pos hle] at h
  simp only [odoUnif]
  exact h

/-- The neighbour pair in a direction `k` other than the mid direction `m`: the
two neighbours of `p` at `t - 1` are dominated by the two neighbours of `p + e_m`
at `t`. -/
theorem nbr_pair_le (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (ht : 1 ≤ t)
    (hS : RegStrongFacet d M (t - 1)) (p : Site d) (hp : inPos d M p) (m : Fin d)
    (hpm : p m = 1)
    (htop : odoUnif d (2 * M) t p = odoUnif d (2 * M) (t - 1) p + 1)
    (hmid : odoUnif d (2 * M) t (p + unit m) = odoUnif d (2 * M) (t - 1) p)
    (k : Fin d) (hkm : k ≠ m) :
    odoUnif d (2 * M) (t - 1) (p + unit k) + odoUnif d (2 * M) (t - 1) (p - unit k)
      ≤ odoUnif d (2 * M) t (p + unit m + unit k)
        + odoUnif d (2 * M) t (p + unit m - unit k) := by
  have ht1 : t - 1 + 1 = t := by omega
  have hmk : m ≠ k := fun h => hkm h.symm
  -- the plus neighbour
  have hplus : odoUnif d (2 * M) (t - 1) (p + unit k)
      ≤ odoUnif d (2 * M) t (p + unit m + unit k) := by
    have hpt : p + unit m + unit k = p + unit k + unit m := by abel
    rw [hpt]
    by_cases hkM : p k + 1 ≤ (M : ℤ)
    · have hz : inPos d M (p + unit k) := by
        intro l
        by_cases hl : l = k
        · subst hl
          rw [add_unit_self]
          have := (hp l).1
          constructor <;> omega
        · rw [add_unit_other d p k l hl]
          exact hp l
      have hzm : (p + unit k) m = 1 := by rw [add_unit_other d p k m hmk, hpm]
      have h2 : ∃ l, 2 ≤ (p + unit k) l :=
        ⟨k, by rw [add_unit_self]; have := (hp k).1; omega⟩
      have h := strong_raw_le d M (t - 1) hd (by omega) hS (p + unit k) hz m hzm h2
      rw [ht1] at h
      exact h
    · have hoff : ¬ inCube d (2 * M) (p + unit k) := by
        intro hc
        have h := (hc k).2
        rw [add_unit_self, hiCoord_two_mul] at h
        exact hkM h
      have h0 : odoUnif d (2 * M) (t - 1) (p + unit k) = 0 :=
        odo_eq_zero_outside d (2 * M) _ (t - 1) _ hoff
      rw [h0]
      exact odo_nonneg d (2 * M) _ t _
  -- the minus neighbour
  have hminus : odoUnif d (2 * M) (t - 1) (p - unit k)
      ≤ odoUnif d (2 * M) t (p + unit m - unit k) := by
    have hpt : p + unit m - unit k = p - unit k + unit m := by abel
    have hpk1 := (hp k).1
    rcases (show p k = 1 ∨ p k = 2 ∨ 3 ≤ p k by omega) with h1 | h2 | h3
    · -- reflection in the coordinate `k`
      rw [odoUnif_sub_unit_of_one M (t - 1) p k h1]
      have hk' : (p + unit m) k = 1 := by rw [add_unit_other d p m k hkm, h1]
      rw [odoUnif_sub_unit_of_one M t (p + unit m) k hk', hmid]
    · -- the swap of the coordinates `k` and `m`
      rw [hpt]
      have hzk : (p - unit k) k = (p - unit k) m := by
        rw [sub_unit_self, sub_unit_other d p k m hmk, h2, hpm]
        norm_num
      rw [odoUnif_add_unit_swap M t (p - unit k) k m hkm hzk]
      have hback : p - unit k + unit k = p := by abel
      rw [hback, htop]
      have hfd := odo_first_diff d M hd (by omega) (t - 1) k (p - unit k)
        (by rw [sub_unit_self]; omega)
      rw [hback, sub_unit_self, h2] at hfd
      linarith
    · -- strong facet compatibility at `t - 1`
      rw [hpt]
      have hz : inPos d M (p - unit k) := by
        intro l
        by_cases hl : l = k
        · subst hl
          rw [sub_unit_self]
          have := (hp l).2
          constructor <;> omega
        · rw [sub_unit_other d p k l hl]
          exact hp l
      have hzm : (p - unit k) m = 1 := by rw [sub_unit_other d p k m hmk, hpm]
      have h2 : ∃ l, 2 ≤ (p - unit k) l := ⟨k, by rw [sub_unit_self]; omega⟩
      have h := strong_raw_le d M (t - 1) hd (by omega) hS (p - unit k) hz m hzm h2
      rw [ht1] at h
      exact h
  linarith

/-- The neighbour pair in the mid direction `m`. -/
theorem mid_pair_le (d M t : ℕ) (p : Site d) (m : Fin d) (hpm : p m = 1)
    (htop : odoUnif d (2 * M) t p = odoUnif d (2 * M) (t - 1) p + 1)
    (hprev : odoUnif d (2 * M) (t - 1) (p + unit m) ≤ odoUnif d (2 * M) (t - 1) p)
    (htwo : odoUnif d (2 * M) t p - odoUnif d (2 * M) t (p + unit m + unit m) ≤ 2) :
    odoUnif d (2 * M) (t - 1) (p + unit m) + odoUnif d (2 * M) (t - 1) (p - unit m)
      ≤ odoUnif d (2 * M) t (p + unit m + unit m)
        + odoUnif d (2 * M) t (p + unit m - unit m) := by
  rw [odoUnif_sub_unit_of_one M (t - 1) p m hpm, add_sub_cancel_right]
  linarith

/-- The Laplacian comparison: the Laplacian of `p + e_m` at `t` dominates the
Laplacian of `p` at `t - 1`. -/
theorem lap_le_of_prev (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (ht : 1 ≤ t)
    (hS : RegStrongFacet d M (t - 1)) (p : Site d) (hp : inPos d M p) (m : Fin d)
    (hpm : p m = 1)
    (htop : odoUnif d (2 * M) t p = odoUnif d (2 * M) (t - 1) p + 1)
    (hmid : odoUnif d (2 * M) t (p + unit m) = odoUnif d (2 * M) (t - 1) p)
    (hprev : odoUnif d (2 * M) (t - 1) (p + unit m) ≤ odoUnif d (2 * M) (t - 1) p)
    (htwo : odoUnif d (2 * M) t p - odoUnif d (2 * M) t (p + unit m + unit m) ≤ 2) :
    lap (odoUnif d (2 * M) (t - 1)) p ≤ lap (odoUnif d (2 * M) t) (p + unit m) := by
  have hsum : nbrSum (odoUnif d (2 * M) (t - 1)) p
      ≤ nbrSum (odoUnif d (2 * M) t) (p + unit m) := by
    unfold nbrSum
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hkm : k = m
    · subst hkm
      exact mid_pair_le d M t p k hpm htop hprev htwo
    · exact nbr_pair_le d M t hd hM ht hS p hp m hpm htop hmid k hkm
  unfold lap
  rw [hmid]
  linarith

/-- The mid facet point is the first facet point moved one step in the mid direction. -/
theorem facetPoint_one_add_mid {i j : ℕ} (x : Fin i → ℤ) :
    facetPoint x 1 j + unit (Fin.castAdd j (Fin.last i)) = facetPoint x 2 j := by
  rw [facetPoint_add_mid_point x 1]
  norm_num

theorem facetPoint_one_add_mid_two {i j : ℕ} (x : Fin i → ℤ) :
    facetPoint x 1 j + unit (Fin.castAdd j (Fin.last i)) + unit (Fin.castAdd j (Fin.last i))
      = facetPoint x 3 j := by
  rw [facetPoint_one_add_mid, facetPoint_add_mid_point x 2]
  norm_num

/-- The regime of the clause at `t` gives the regime at `t - 1`. -/
theorem regime_prev {d M t : ℕ} {i : ℕ}
    (hreg : (t : ℕ∞) < toppleTime d M ∨ (1 ≤ i ∧ toppleTime d M ≤ (t : ℕ∞))) :
    ((t - 1 : ℕ) : ℕ∞) < toppleTime d M ∨
      (1 ≤ i ∧ toppleTime d M ≤ ((t - 1 : ℕ) : ℕ∞)) := by
  rcases hreg with h | h
  · left
    exact lt_of_le_of_lt (Nat.cast_le.mpr (Nat.sub_le t 1)) h
  · by_cases h' : ((t - 1 : ℕ) : ℕ∞) < toppleTime d M
    · exact Or.inl h'
    · exact Or.inr ⟨h.1, not_lt.mp h'⟩

/-- One step back from a facet gap: the two points had the same value at `t - 1`,
the first toppled from `t - 1` to `t` and the second did not. -/
theorem facet_prev (i j M t : ℕ) (hM : 2 ≤ M) (ht : 1 ≤ t)
    (hS : RegStrongFacet (i + 1 + j) M (t - 1)) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (hgap : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) + 1 := by
  have ht1 : t - 1 + 1 = t := by omega
  have hfd := odo_first_diff (i + 1 + j) M (by omega) (by omega) (t - 1)
    (Fin.castAdd j (Fin.last i)) (facetPoint x 1 j) (by rw [facetPoint_mid])
  rw [facetPoint_one_add_mid, facetPoint_mid] at hfd
  have hstep := (odo_succ_sub_bounds (i + 1 + j) (2 * M) (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ))
    (t - 1) (facetPoint x 1 j)).2
  rw [ht1] at hstep
  have hmono := odo_mono (i + 1 + j) (2 * M) (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ))
    (show t - 1 ≤ t by omega) (facetPoint x 2 j)
  simp only [odoUnif] at hfd hgap ⊢
  by_cases hg : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1
  · exfalso
    have hc := hS i j rfl x hx2 hxs (regime_prev hreg) hg
    rw [ht1] at hc
    simp only [odoUnif] at hc hg
    omega
  · simp only [odoUnif] at hg
    omega

/-- The second facet point topples at `t`: its Laplacian at `t` dominates the
Laplacian at `t - 1` of the first point, which toppled. -/
theorem facet_mid_topples (i j M t : ℕ) (hM : 2 ≤ M) (ht : 1 ≤ t)
    (hS : RegStrongFacet (i + 1 + j) M (t - 1)) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (htwo : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2)
    (hgap : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 := by
  obtain ⟨h1, h2, h3⟩ := facet_prev i j M t hM ht hS x hx2 hxs hreg hgap
  set m : Fin (i + 1 + j) := Fin.castAdd j (Fin.last i) with hm
  have hmid : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j + unit m)
      = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) := by
    rw [hm, facetPoint_one_add_mid, h2]
  have hprev : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j + unit m)
      ≤ odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) := by
    rw [hm, facetPoint_one_add_mid, h1]
  have htwo' : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j + unit m + unit m) ≤ 2 := by
    rw [hm, facetPoint_one_add_mid_two]
    exact htwo
  have hcmp := lap_le_of_prev (i + 1 + j) M t (by omega) hM ht hS (facetPoint x 1 j) hxs.1 m
    (by rw [hm, facetPoint_mid]) h3 hmid hprev htwo'
  have hlap0 := lap_nonneg_of_topple M t ht (facetPoint x 1 j) h3
  rw [hm, facetPoint_one_add_mid] at hcmp
  have hcube : inCube (i + 1 + j) (2 * M) (facetPoint x 2 j) := by
    intro l
    rw [loCoord_two_mul, hiCoord_two_mul, ← facetPoint_one_add_mid]
    have hl := hxs.1 l
    by_cases hlm : l = Fin.castAdd j (Fin.last i)
    · subst hlm
      rw [add_unit_self, facetPoint_mid]
      constructor <;> omega
    · rw [add_unit_other _ _ _ _ hlm]
      constructor <;> omega
  exact topple_of_lap_nonneg M t _ hcube (by linarith)

/-- With a nonempty head, once `t - 1` has reached `τ_{M-1}`, strong topple control at
`t - 1` freezes the first facet point, which toppled from `t - 1` to `t`. -/
theorem facet_head_stays_late (i j M t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hT : RegTopple (i + 1 + j) M (t - 1))
    (hlate : toppleTime (i + 1 + j) (M - 1) ≤ ((t - 1 : ℕ) : ℕ∞))
    (htop : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  have hmax := hT hlate
  have hle := le_simplexMax (i + 1 + j) M
    (fun w => odoUnif (i + 1 + j) (2 * M) (t - 1 + 2) w
      - odoUnif (i + 1 + j) (2 * M) (t - 1) w) (facetPoint x 1 j) hxs
  rw [show t - 1 + 2 = t + 1 by omega] at hle hmax
  have hmono := odo_mono (i + 1 + j) (2 * M) (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ))
    (show t ≤ t + 1 by omega) (facetPoint x 1 j)
  simp only [odoUnif] at hle hmono htop hmax ⊢
  omega

/-! ### The reflecting boundary before `τ_{M-1}` -/

private theorem regEarlier_dim {d M t d' M' t' : ℕ} (h : d' < d) : regEarlier d M t d' M' t' :=
  Or.inl h

private theorem regEarlier_side {d M t d' M' t' : ℕ} (hd : d' ≤ d) (hM : M' < M) :
    regEarlier d M t d' M' t' := by
  rcases Nat.lt_or_eq_of_le hd with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hM⟩)

private theorem regEarlier_time {d M t d' t' : ℕ} (hd : d' ≤ d) (ht : t' < t) :
    regEarlier d M t d' M t' := by
  rcases Nat.lt_or_eq_of_le hd with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h, rfl, ht⟩)

/-- Self-similarity from scale `M` to scale `M - 1`, in the shifted form. -/
theorem consist_shift_one {D M s : ℕ} (hM : 2 ≤ M) (hC : RegConsist D M s)
    (hs : (s : ℕ∞) ≤ toppleTime D (M - 1)) (z : Site D) (hz : inSimplex D M z)
    (hz1 : ∀ k, 1 < z k) :
    odoUnif D (2 * M) s z = odoUnif D (2 * (M - 1)) s (fun k => z k - 1) := by
  have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have h := hC (M - 1) (by omega) (by omega) hs z hz (fun k => by
    rw [hcast]
    have := hz1 k
    omega)
  have hpt : (fun k => z k - ((M : ℤ) - ((M - 1 : ℕ) : ℤ))) = fun k => z k - 1 := by
    funext k
    rw [hcast]
    ring
  rw [hpt] at h
  exact h

/-- The neighbour-sum identity of the one-step self-similarity at a point all of
whose coordinates are at least two, given the reflecting boundary identity at
each neighbour with a coordinate equal to one. -/
theorem nbrSum_selfsim_two (D m s : ℕ) (hm : 2 ≤ m) (y : Site D) (hy : inSimplex D m y)
    (hy2 : ∀ k, 2 ≤ y k)
    (hstep : ∀ z : Site D, inSimplex D m z → (∀ k : Fin D, 1 < z k) →
      odoUnif D (2 * m) s z = odoUnif D (2 * (m - 1)) s (fun k => z k - 1))
    (hrefl : ∀ k : Fin D, y k = 2 →
      odoUnif D (2 * m) s (y - unit k) = odoUnif D (2 * m) s y) :
    nbrSum (odoUnif D (2 * m) s) y
      = nbrSum (odoUnif D (2 * (m - 1)) s) (fun k => y k - 1) := by
  have hfold : ∀ z : Site D, inCube D (2 * m) z → (∀ k, 2 ≤ z k) →
      inSimplex D m (toSimplexPoint D m z) ∧
        (∀ k : Fin D, 1 < toSimplexPoint D m z k) := by
    intro z hz hz2
    refine ⟨inSimplex_toSimplexPoint D m z hz, fun k => ?_⟩
    rw [toSimplexPoint]
    rw [foldPoint_apply, if_pos (by
      have := hz2 (Tuple.sort (fun i => -(foldPoint D (2 * m) z i)) k); omega)]
    have := hz2 (Tuple.sort (fun i => -(foldPoint D (2 * m) z i)) k)
    omega
  have hshift : ∀ z : Site D, inCube D (2 * m) z → (∀ k, 2 ≤ z k) →
      odoUnif D (2 * m) s z = odoUnif D (2 * (m - 1)) s (fun k => z k - 1) := by
    intro z hz hz2
    obtain ⟨hf, hg⟩ := hfold z hz hz2
    rw [← odoUnif_toSimplexPoint D m s z, hstep _ hf hg,
      odoUnif_toSimplexPoint_sub D m s z (fun k => by have := hz2 k; omega)]
  have hterm : ∀ i : Fin D,
      odoUnif D (2 * m) s (y + unit i) + odoUnif D (2 * m) s (y - unit i)
        = odoUnif D (2 * (m - 1)) s (fun k => (y + unit i) k - 1)
          + odoUnif D (2 * (m - 1)) s (fun k => (y - unit i) k - 1) := by
    intro i
    congr 1
    · by_cases hlt : y i < (m : ℤ)
      · refine hshift _ ?_ ?_
        · intro k
          rw [loCoord_two_mul, hiCoord_two_mul]
          have h1 := hy.1 k
          by_cases hk : k = i
          · subst hk
            rw [add_unit_self]
            constructor <;> omega
          · rw [add_unit_other _ _ _ _ hk]
            constructor <;> omega
        · intro k
          by_cases hk : k = i
          · subst hk
            rw [add_unit_self]
            have := hy2 k
            omega
          · rw [add_unit_other _ _ _ _ hk]
            exact hy2 k
      · have hyi : y i = (m : ℤ) := by
          have h1 := hy.1 i
          omega
        have hout : odoUnif D (2 * m) s (y + unit i) = 0 := by
          rw [odoUnif, odo_eq_zero_outside]
          intro hc
          have h1 := hc i
          rw [loCoord_two_mul, hiCoord_two_mul, add_unit_self, hyi] at h1
          omega
        have hout' : odoUnif D (2 * (m - 1)) s (fun k => (y + unit i) k - 1) = 0 := by
          rw [odoUnif, odo_eq_zero_outside]
          intro hc
          have h1 := hc i
          rw [loCoord_two_mul, hiCoord_two_mul] at h1
          simp only at h1
          rw [add_unit_self, hyi, Nat.cast_sub (by omega)] at h1
          norm_num at h1
        rw [hout, hout']
    · by_cases h2 : y i = 2
      · rw [hrefl i h2, hstep y hy (fun k => by have := hy2 k; omega)]
        have hpt : (fun k => (y - unit i) k - 1) = (fun k => y k - 1) - unit i := by
          funext k
          simp only [Pi.sub_apply]
          ring
        rw [hpt, odoUnif_sub_unit_of_one (m - 1) s (fun k => y k - 1) i (by
          show y i - 1 = 1
          omega)]
      · refine hshift _ ?_ ?_
        · intro k
          rw [loCoord_two_mul, hiCoord_two_mul]
          have h1 := hy.1 k
          by_cases hk : k = i
          · subst hk
            rw [sub_unit_self]
            constructor <;> omega
          · rw [sub_unit_other _ _ _ _ hk]
            constructor <;> omega
        · intro k
          by_cases hk : k = i
          · subst hk
            rw [sub_unit_self]
            have := hy2 k
            omega
          · rw [sub_unit_other _ _ _ _ hk]
            exact hy2 k
  simp only [nbrSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i]
  congr 1 <;> (congr 1; funext k; simp only [Pi.add_apply, Pi.sub_apply]; ring)

/-- The one-step self-similarity at a point all of whose coordinates are at least
two, from self-similarity and the reflecting boundary identity one step earlier. -/
theorem selfsim_step_two (D m s : ℕ) (hm : 2 ≤ m) (y : Site D) (hy : inSimplex D m y)
    (hy2 : ∀ k, 2 ≤ y k)
    (hstep : ∀ z : Site D, inSimplex D m z → (∀ k : Fin D, 1 < z k) →
      odoUnif D (2 * m) s z = odoUnif D (2 * (m - 1)) s (fun k => z k - 1))
    (hrefl : ∀ k : Fin D, y k = 2 →
      odoUnif D (2 * m) s (y - unit k) = odoUnif D (2 * m) s y) :
    odoUnif D (2 * m) (s + 1) y = odoUnif D (2 * (m - 1)) (s + 1) (fun k => y k - 1) := by
  have hn := nbrSum_selfsim_two D m s hm y hy hy2 hstep hrefl
  have hv := hstep y hy (fun k => by have := hy2 k; omega)
  have hc1 : inCube D (2 * m) y := inSimplex_inCube D m y hy
  have hc2 : inCube D (2 * (m - 1)) (fun k => y k - 1) := by
    intro k
    rw [loCoord_two_mul, hiCoord_two_mul, Nat.cast_sub (by omega)]
    have h1 := hy.1 k
    have := hy2 k
    simp only
    constructor <;> omega
  have e1 := odo_succ_eq D (2 * m) (fun _ => 2 * (D : ℤ)) s y hc1
  have e2 := odo_succ_eq D (2 * (m - 1)) (fun _ => 2 * (D : ℤ)) s _ hc2
  have hs : sandp D (2 * m) (fun _ => 2 * (D : ℤ)) s y
      = sandp D (2 * (m - 1)) (fun _ => 2 * (D : ℤ)) s (fun k => y k - 1) := by
    simp only [sandp, lap]
    rw [← odoUnif_fun_eq, ← odoUnif_fun_eq, hn, hv]
  simp only [odoUnif] at hv ⊢
  rw [e1, e2, hs, hv]

/-- The topple time of scale `M - 1` does not increase with the dimension, from
dimensional reduction at scale `M - 1`. -/
theorem toppleTime_le_of_dim_le (d M t : ℕ) (hM : 3 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    ∀ n e : ℕ, 1 ≤ e → e + n = d → toppleTime d (M - 1) ≤ toppleTime e (M - 1) := by
  intro n
  induction n with
  | zero =>
    intro e _ he
    rw [← he]
    rfl
  | succ n ih =>
    intro e he hen
    have h1 := ih (e + 1) (by omega) (by omega)
    have h2 : toppleTime (e + 1) (M - 1) ≤ toppleTime e (M - 1) :=
      toppleTime_mono_dim_le e (M - 1) he (by omega)
        (fun t' y hy => (hprior (e + 1) (M - 1) t'
          (regEarlier_side (by omega) (by omega)) (by omega) (by omega)).2 e he rfl y hy)
        (fun e' he' hlt t' y hy => (hprior (e' + 1) (M - 1) t'
          (regEarlier_side (by omega) (by omega)) (by omega) (by omega)).2 e' he' rfl y hy)
    exact h1.trans h2

/-- Dimensional reduction peels the tail of ones off a facet point at one time. -/
theorem facet_reduce_at (i M t : ℕ) (x : Fin i → ℤ) (c : ℤ) :
    ∀ j : ℕ, (∀ k, k < j → DimRedAt (i + 1 + k + 1) M t) →
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x c j)
        = odoUnif (i + 1) (2 * M) t (Fin.snoc x c) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [facetPoint_zero]
  | succ j ih =>
    intro hD
    have h := odoUnif_snoc_of_reduction (i + 1 + j) M t
      (fun w hw => hD j (by omega) (i + 1 + j) (by omega) rfl w hw) (facetPoint x c j)
    rw [facetPoint_succ]
    show odoUnif (i + 1 + j + 1) (2 * M) t (Fin.snoc (facetPoint x c j) 1) = _
    rw [h, ih (fun k hk => hD k (by omega))]

/-- The head of a facet point, shifted down by one, lies in the smaller simplex. -/
theorem inSimplex_sub_one {i M : ℕ} (x : Fin i → ℤ) (hx : inSimplex i M x)
    (hx2 : ∀ a, 2 ≤ x a) : inSimplex i (M - 1) (fun k => x k - 1) := by
  refine ⟨fun k => ?_, fun a b hab => ?_⟩
  · have h1 := hx.1 k
    have := hx2 k
    have hM : 1 ≤ M := by omega
    rw [Nat.cast_sub hM]
    constructor <;> push_cast <;> omega
  · have := hx.2 a b hab
    simp only
    omega

/-- The reflecting boundary identity at one time, from self-similarity at the two
scales and dimensional reduction. -/
theorem reflecting_boundary_at (i M s : ℕ) (hi : 1 ≤ i) (hM : 3 ≤ M) (x : Fin i → ℤ)
    (hx : inSimplex i M x) (hx2 : ∀ a, 2 ≤ x a)
    (hself : odoUnif (i + 1) (2 * M) s (Fin.snoc x 2)
      = odoUnif (i + 1) (2 * (M - 1)) s (Fin.snoc (fun k => x k - 1) 1))
    (hredM1 : DimRedAt (i + 1) (M - 1) s) (hredM : DimRedAt (i + 1) M s)
    (hC : RegConsist i M s) (hs : (s : ℕ∞) ≤ toppleTime i (M - 1)) :
    odoUnif (i + 1) (2 * M) s (Fin.snoc x 1) = odoUnif (i + 1) (2 * M) s (Fin.snoc x 2) := by
  have hx1 : ∀ k, 1 < x k := fun k => by have := hx2 k; omega
  exact (odo_reflecting_boundary i M s hi (by omega) x hx hx1 hself
    (hredM1 i hi rfl _ (inSimplex_sub_one x hx hx2)) (hredM i hi rfl x hx)
    (consist_shift_one (by omega) hC hs x hx hx1)).symm

/-- The shifted point `(x, 2) - 1` is `(x - 1, 1)`. -/
theorem snoc_two_sub_one {i : ℕ} (x : Fin i → ℤ) :
    (fun k => (Fin.snoc x 2 : Site (i + 1)) k - 1) = Fin.snoc (fun k => x k - 1) 1 := by
  funext k
  refine Fin.lastCases ?_ (fun a => ?_) k
  · simp only [Fin.snoc_last]
    norm_num
  · simp only [Fin.snoc_castSucc]

/-- The neighbours of `(x, 2)` with a coordinate equal to one: each is the point
`(x, 1)` up to a swap of coordinates. -/
theorem odoUnif_snoc_two_sub_unit {i M s : ℕ} (x : Fin i → ℤ) (k : Fin (i + 1))
    (hk : (Fin.snoc x 2 : Site (i + 1)) k = 2) :
    odoUnif (i + 1) (2 * M) s (Fin.snoc x 2 - unit k)
      = odoUnif (i + 1) (2 * M) s (Fin.snoc x 1) := by
  induction k using Fin.lastCases with
  | last =>
    rw [← snoc_sub_unit_last]
    norm_num
  | cast a =>
    rw [Fin.snoc_castSucc] at hk
    have e1 : (Fin.snoc x 2 : Site (i + 1)) - unit (Fin.castSucc a)
        = Fin.snoc (x - unit a) 1 + unit (Fin.last i) := by
      rw [← snoc_sub_unit, ← snoc_add_unit_last]
      norm_num
    have e2 : (Fin.snoc x 1 : Site (i + 1)) = Fin.snoc (x - unit a) 1 + unit (Fin.castSucc a) := by
      rw [← snoc_add_unit]
      congr 1
      funext l
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e1, e2]
    refine odoUnif_add_unit_swap M s _ _ _ ?_ ?_
    · intro h
      exact Fin.castSucc_ne_last a h
    · rw [Fin.snoc_castSucc, Fin.snoc_last, sub_unit_self, hk]
      norm_num

/-- Before `t - 1` reaches `τ_{M-1}`, a facet point with a nonempty head has the same
value as its mid neighbour: the reflecting boundary identity at time `t`, obtained
from the identity and self-similarity at `t - 1` by one toppling step. -/
theorem facet_no_gap_early (i j M t : ℕ) (hM : 2 ≤ M) (hi : 1 ≤ i) (ht : 1 ≤ t)
    (hprior : ∀ d' M' t' : ℕ, regEarlier (i + 1 + j) M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hdimred : DimRedAt (i + 1 + j) M t)
    (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hearly : ¬ toppleTime (i + 1 + j) (M - 1) ≤ ((t - 1 : ℕ) : ℕ∞)) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) := by
  -- at `t = 1` the odometer is one on the whole cube
  rcases Nat.lt_or_ge t 2 with ht1 | ht2
  · have ht1' : t = 1 := by omega
    subst ht1'
    have hs2 : inSimplex (i + 1 + j) M (facetPoint x 2 j) :=
      inSimplex_facetPoint_two_of_inSimplex_facetPoint_one x hM hx2 hxs le_rfl
    rw [odoUnif_one_eq_one _ M _ (inSimplex_inCube _ M _ hxs),
      odoUnif_one_eq_one _ M _ (inSimplex_inCube _ M _ hs2)]
  -- below `τ_{M-1}` with `t ≥ 2` the scale is at least three
  have hM3 : 3 ≤ M := by
    by_contra h
    have hM2 : M = 2 := by omega
    subst hM2
    apply hearly
    rw [show (2 - 1 : ℕ) = 1 from rfl, toppleTime_one_eq_one _ (by omega)]
    exact_mod_cast (show 1 ≤ t - 1 by omega)
  have htau : (t : ℕ∞) ≤ toppleTime (i + 1 + j) (M - 1) := by
    have h := lt_of_not_ge hearly
    induction h' : toppleTime (i + 1 + j) (M - 1) using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      rw [h'] at h
      have : t - 1 < n := by exact_mod_cast h
      exact_mod_cast (show t ≤ n by omega)
  have htau_le := toppleTime_le_of_dim_le (i + 1 + j) M t hM3 hprior
  have htau1 : (t : ℕ∞) ≤ toppleTime (i + 1) (M - 1) :=
    htau.trans (htau_le j (i + 1) (by omega) rfl)
  have htau0 : (t : ℕ∞) ≤ toppleTime i (M - 1) :=
    htau.trans (htau_le (j + 1) i hi (by omega))
  have htau1' : ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (i + 1) (M - 1) :=
    le_trans (by exact_mod_cast (Nat.sub_le t 1)) htau1
  have htau0' : ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime i (M - 1) :=
    le_trans (by exact_mod_cast (Nat.sub_le t 1)) htau0
  -- the facts in dimension `i + 1` and `i`
  have hx : inSimplex i M x := peel_inSimplex x M (by omega) hxs
  have hy : inSimplex (i + 1) M (Fin.snoc x 2) := inSimplex_snoc_two_local x hx hx2 hM
  have hy2 : ∀ k, 2 ≤ (Fin.snoc x 2 : Site (i + 1)) k := by
    intro k
    induction k using Fin.lastCases with
    | last => rw [Fin.snoc_last]
    | cast a => rw [Fin.snoc_castSucc]; exact hx2 a
  have hP1 := hprior (i + 1) M (t - 1) (regEarlier_time (by omega) (by omega)) (by omega) hM
  have hP0 := hprior i M (t - 1) (regEarlier_time (by omega) (by omega)) hi hM
  have hQ1 := hprior (i + 1) (M - 1) (t - 1) (regEarlier_side (by omega) (by omega))
    (by omega) (by omega)
  have hR1 := hprior (i + 1) (M - 1) t (regEarlier_side (by omega) (by omega))
    (by omega) (by omega)
  have hR0 := hprior i M t (regEarlier_dim (by omega)) hi hM
  have hredM : DimRedAt (i + 1) M t := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      exact hdimred
    · exact (hprior (i + 1) M t (regEarlier_dim (by omega)) (by omega) hM).2
  -- the reflecting boundary identity at `t - 1`
  have hrb_prev := reflecting_boundary_at i M (t - 1) hi hM3 x hx hx2
    (by
      rw [← snoc_two_sub_one]
      exact consist_shift_one hM hP1.1.1 htau1' _ hy (fun k => by have := hy2 k; omega))
    hQ1.2 hP1.2 hP0.1.1 htau0'
  -- self-similarity at `(x, 2)` at time `t`
  have hself : odoUnif (i + 1) (2 * M) t (Fin.snoc x 2)
      = odoUnif (i + 1) (2 * (M - 1)) t (Fin.snoc (fun k => x k - 1) 1) := by
    rw [← snoc_two_sub_one]
    have h := selfsim_step_two (i + 1) M (t - 1) hM (Fin.snoc x 2) hy hy2
      (consist_shift_one hM hP1.1.1 htau1')
      (fun k hk => by rw [odoUnif_snoc_two_sub_unit x k hk, hrb_prev])
    rw [show t - 1 + 1 = t by omega] at h
    exact h
  have hrb := reflecting_boundary_at i M t hi hM3 x hx hx2 hself hR1.2 hredM hR0.1.1 htau0
  -- back to dimension `i + 1 + j`
  have hD : ∀ k, k < j → DimRedAt (i + 1 + k + 1) M t := by
    intro k hk
    rcases Nat.lt_or_ge (k + 1) j with hlt | hge
    · exact (hprior (i + 1 + k + 1) M t (regEarlier_dim (by omega)) (by omega) hM).2
    · have hkj : i + 1 + k + 1 = i + 1 + j := by omega
      rw [hkj]
      exact hdimred
  rw [facet_reduce_at i M t x 1 j hD, facet_reduce_at i M t x 2 j hD, hrb]

/-- Strong facet compatibility at one triple, the `hfacet_step` input of
`reg_induction`. -/
theorem facet_step_of_earlier (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hdimred : DimRedAt d M t) (hderiv : RegStrongDeriv d M t) :
    RegStrongFacet d M t := by
  intro i j hij x hx2 hxs hreg hgap
  subst hij
  -- at `t = 0` the odometer vanishes and there is no gap
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · subst ht0
    exfalso
    have h0 : ∀ y, odoUnif (i + 1 + j) (2 * M) 0 y = 0 := fun _ => rfl
    rw [h0, h0] at hgap
    omega
  have hprev := hprior (i + 1 + j) M (t - 1) (Or.inr (Or.inr ⟨rfl, rfl, by omega⟩))
    (by omega) hM
  have hS : RegStrongFacet (i + 1 + j) M (t - 1) := hprev.1.2.2.2.1
  obtain ⟨_, _, h3⟩ := facet_prev i j M t hM ht hS x hx2 hxs hreg hgap
  refine ⟨?_, facet_mid_topples i j M t hM ht hS x hx2 hxs hreg
    (hderiv i j rfl x hx2 hxs hreg) hgap⟩
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · subst hi0
    exact odo_succ_facetPoint_zero_of x t hgap
  by_cases hlate : toppleTime (i + 1 + j) (M - 1) ≤ ((t - 1 : ℕ) : ℕ∞)
  · exact facet_head_stays_late i j M t ht x hxs hprev.1.2.2.2.2 hlate h3
  · exfalso
    have h := facet_no_gap_early i j M t hM hi ht hprior hdimred x hx2 hxs hlate
    omega

end DimRed
