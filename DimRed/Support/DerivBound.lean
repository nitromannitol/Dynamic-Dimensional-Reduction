import DimRed.Support.NonnegativeUpdate
/-
The derivative bound of `dimred.tex:531-538`: if the odometer at the corner
`(M, 1_{d-1})` never exceeds `k M`, then `v_t(x) - v_t(x + e_j) ≤ k x_j`
everywhere.

Two ingredients.  `odo_le_of_le` turns axis monotonicity into a comparison for
the coordinatewise order on the sorted domain, by walking from the larger point
to the smaller one along single reflection steps, always lowering the last
coordinate at which the two differ; that step stays inside the domain exactly
because the smaller point is sorted.  `odo_deriv_bound` is then the induction of
`dimred.tex:289-294` again: the difference grows by at most one per step, so the
only case is a difference that has already reached `k x_j`, and there the
recursion compares the two neighbour sums term by term.  The `2d` terms pair up
as `d - 1` copies of `2 k x_j` and one copy of `k (x_j + 1) + k (x_j - 1)`.

The corner hypothesis enters where the step leaves the hypercube: there
`x_j = M`, the far value is the padded `0`, and the near value is at most the
corner value by `odo_le_of_le`.
-/
import DimRed.Support.AxisStep

namespace DimRed

open LatticeProb

section Order

variable (d M : ℕ)

/-- Axis monotonicity in the coordinatewise order: on the sorted domain the
odometer is largest at the smallest point. -/
theorem odo_le_of_le (hd : 1 ≤ d) (c : ℤ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) (t : ℕ) :
    ∀ (n : ℕ) (x y : Site d), inSimplex d M x → inSimplex d M y → (∀ i, y i ≤ x i) →
      (∑ i, (x i - y i)).toNat = n →
      odo d (2 * M) (fun _ => c) t x ≤ odo d (2 * M) (fun _ => c) t y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hx hy hle hn
  by_cases heq : ∀ i, x i = y i
  · rw [funext heq]
  · have hne : (Finset.univ.filter (fun i => y i < x i)).Nonempty := by
      simp only [not_forall] at heq
      obtain ⟨a, ha⟩ := heq
      exact ⟨a, by simp [lt_of_le_of_ne (hle a) (Ne.symm ha)]⟩
    set i := (Finset.univ.filter (fun i => y i < x i)).max' hne with hidef
    have hmem : i ∈ Finset.univ.filter (fun i => y i < x i) := Finset.max'_mem _ hne
    have hilt : y i < x i := by simpa using hmem
    have hbig : ∀ l, i < l → y l = x l := by
      intro l hl
      by_contra hne'
      have hlm : l ∈ Finset.univ.filter (fun i => y i < x i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne (hle l) hne'
      exact absurd (Finset.le_max' _ l hlm) (not_le.mpr hl)
    set z : Site d := x - unit i with hzdef
    have hzi : z i = x i - 1 := by rw [hzdef, sub_unit_self]
    have hzl : ∀ l, l ≠ i → z l = x l := fun l hl => by rw [hzdef, sub_unit_other _ _ _ _ hl]
    have hyi : 1 ≤ y i := (hy.1 i).1
    have hzy : ∀ l, y l ≤ z l := by
      intro l
      by_cases hl : l = i
      · rw [hl, hzi]; omega
      · rw [hzl l hl]; exact hle l
    have hzS : inSimplex d M z := by
      constructor
      · intro l
        by_cases hl : l = i
        · rw [hl, hzi]
          have h1 := (hx.1 i).2
          exact ⟨by omega, by omega⟩
        · rw [hzl l hl]; exact hx.1 l
      · intro a b hab
        by_cases hbi : b = i
        · by_cases hai : a = i
          · rw [hai, hbi]
          · rw [hbi, hzi, hzl a hai]
            have h := hx.2 a b hab
            rw [hbi] at h
            omega
        · rw [hzl b hbi]
          by_cases hai : a = i
          · rw [hai, hzi]
            have hab' : a ≠ b := fun h => hbi (h ▸ hai)
            have hlt : i < b := by
              have hlt' : a < b := lt_of_le_of_ne hab hab'
              rwa [hai] at hlt'
            have h1 : y b = x b := hbig b hlt
            have h2 := hy.2 a b hab
            rw [hai] at h2
            omega
          · rw [hzl a hai]; exact hx.2 a b hab
    have hstep : odo d (2 * M) (fun _ => c) t x ≤ odo d (2 * M) (fun _ => c) t z := by
      have e : z + unit i = x := by rw [hzdef]; abel
      have h := odo_axis_refl d M hd c hc0 hc1 t z i (by rw [hzi]; omega)
      rwa [e] at h
    have hkey : ∀ l, z l - y l = (x l - y l) - (if l = i then 1 else 0) := by
      intro l
      by_cases hl : l = i
      · rw [hl, hzi, if_pos rfl]; ring
      · rw [hzl l hl, if_neg hl]; ring
    have hsum : (∑ l, (z l - y l)) = (∑ l, (x l - y l)) - 1 := by
      rw [Finset.sum_congr rfl (fun l _ => hkey l), Finset.sum_sub_distrib]
      congr 1
      simp
    have hpos : 0 < (∑ l, (x l - y l)) := by
      have hnn : ∀ l ∈ Finset.univ, (0 : ℤ) ≤ x l - y l := fun l _ => by
        have := hle l; omega
      have hi' : (0 : ℤ) < x i - y i := by omega
      exact lt_of_lt_of_le hi' (Finset.single_le_sum hnn (Finset.mem_univ i))
    exact le_trans hstep
      (ih ((∑ l, (z l - y l)).toNat) (by omega) z y hzS hy hzy rfl)

end Order

section Corner

variable (d M : ℕ)

/-- Lowering a coordinate that equals `1` to `0` is a reflection, so it does not
change the odometer. -/
theorem odo_sub_unit_of_one (c : ℤ) (t : ℕ) (x : Site d) (j : Fin d) (h1 : x j = 1) :
    odo d (2 * M) (fun _ => c) t (x - unit j) = odo d (2 * M) (fun _ => c) t x := by
  have hrefl := odo_reflect_coord d M c t (x - unit j) j
  have e : (fun l => if l = j then 1 - (x - unit j) j else (x - unit j) l) = x := by
    funext l
    by_cases hl : l = j
    · rw [if_pos hl, hl, sub_unit_self, h1]; norm_num
    · rw [if_neg hl, sub_unit_other _ _ _ _ hl]
  rw [e] at hrefl
  exact hrefl.symm

/-- A site of the hypercube with a coordinate equal to `M` has odometer at most
the corner value. -/
theorem odo_le_corner (hd : 1 ≤ d) (c : ℤ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) (t : ℕ) (x : Site d) (hx : inCube d (2 * M) x)
    (j : Fin d) (hxj : x j = (M : ℤ)) :
    odo d (2 * M) (fun _ => c) t x
      ≤ odo d (2 * M) (fun _ => c) t (cornerPoint d M) := by
  classical
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    have h := hx j
    rw [loCoord_two_mul, hiCoord_two_mul] at h
    omega
  have hM : 1 ≤ M := by exact_mod_cast hM1
  set y := toSimplexPoint d M x with hy
  have hyS : inSimplex d M y := inSimplex_toSimplexPoint d M x hx
  have hyx : odo d (2 * M) (fun _ => c) t y = odo d (2 * M) (fun _ => c) t x :=
    odo_toSimplexPoint d M (fun _ => c) (isSymmetricPile_const' d (2 * M) c) t x
  -- `M` occurs among the folded coordinates, so the largest coordinate of `y` is `M`
  have hzero : (0 : ℕ) < d := hd
  set i0 : Fin d := ⟨0, hzero⟩ with hi0
  have hfold : foldPoint d (2 * M) x j = (M : ℤ) := by
    rw [foldPoint_apply, if_pos (by omega : (1 : ℤ) ≤ x j), hxj]
  obtain ⟨m, hm⟩ := (Tuple.sort (fun i => -(foldPoint d (2 * M) x i))).surjective j
  have hym : y m = (M : ℤ) := by rw [hy, toSimplexPoint, hm, hfold]
  have hy0 : (M : ℤ) ≤ y i0 := by
    rw [← hym]
    exact hyS.2 i0 m (Fin.le_def.mpr (by simp [hi0]))
  have hcorner : inSimplex d M (cornerPoint d M) := by
    constructor
    · intro l; rw [cornerPoint]; split <;> omega
    · intro a b _
      rw [cornerPoint, cornerPoint]
      split <;> split <;> omega
  have hle : ∀ l, cornerPoint d M l ≤ y l := by
    intro l
    rw [cornerPoint]
    by_cases hl : (l : ℕ) = 0
    · rw [if_pos hl]
      have : l = i0 := by ext; simpa [hi0] using hl
      rw [this]; exact hy0
    · rw [if_neg hl]; exact (hyS.1 l).1
  rw [← hyx]
  exact odo_le_of_le d M hd c hc0 hc1 t _ y (cornerPoint d M) hyS hcorner hle rfl

end Corner

section Derivative

variable (d M : ℕ)

/-- `dimred.tex:531-538`.  Given a bound `k M` on the corner value, the
first difference of the odometer in direction `j` is at most `k x_j`. -/
theorem odo_deriv_bound (hd : 1 ≤ d) (c : ℤ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) (k : ℕ) (hk : 1 ≤ k)
    (hcor : ∀ t, odo d (2 * M) (fun _ => c) t (cornerPoint d M) ≤ (k : ℤ) * (M : ℤ)) :
    ∀ (t : ℕ) (j : Fin d) (x : Site d), 1 ≤ x j →
      odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + unit j)
        ≤ (k : ℤ) * x j := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  intro t
  induction t with
  | zero =>
    intro j x hxj
    have h : (0 : ℤ) ≤ (k : ℤ) * x j := mul_nonneg (by omega) (by omega)
    simpa [odo] using h
  | succ n ih =>
    intro j x hxj
    by_cases hx : inCube d (2 * M) x
    · by_cases hxa : inCube d (2 * M) (x + unit j)
      · rcases lt_or_eq_of_le (ih j x hxj) with hlt | heq
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
              have t1 := ih j (x + unit i) (by rw [hv1]; omega)
              rw [hv1] at t1
              by_cases hx2 : 2 ≤ x j
              · have hv2 : (x - unit i) j = x j - 1 := by rw [hij, sub_unit_self]
                have t2 := ih j (x - unit i) (by rw [hv2]; omega)
                rw [hv2] at t2
                nlinarith [t1, t2]
              · have hx1 : x j = 1 := by omega
                have he : odo d (2 * M) (fun _ => c) n (x - unit i)
                    = odo d (2 * M) (fun _ => c) n x := by
                  rw [hij]; exact odo_sub_unit_of_one d M c n x j hx1
                have he2 : (x - unit i) + unit j = x := by rw [hij]; abel
                rw [he, he2, hx1]
                rw [hx1] at t1
                nlinarith [t1]
            · have hji : j ≠ i := fun h => hij h.symm
              have hv1 : (x + unit i) j = x j := add_unit_other d x i j hji
              have hv2 : (x - unit i) j = x j := sub_unit_other d x i j hji
              have t1 := ih j (x + unit i) (by rw [hv1]; omega)
              have t2 := ih j (x - unit i) (by rw [hv2]; omega)
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
                  + 2 * (d : ℤ) * ((k : ℤ) * x j)) / (2 * (d : ℤ)) :=
            Int.ediv_le_ediv hdpos (by linarith)
          have h2 : (c + nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)
                  + 2 * (d : ℤ) * ((k : ℤ) * x j)) / (2 * (d : ℤ))
              = (c + nbrSum (odo d (2 * M) (fun _ => c) n) (x + unit j)) / (2 * (d : ℤ))
                + (k : ℤ) * x j :=
            Int.add_mul_ediv_left _ _ (ne_of_gt hdpos)
          omega
      · have hxjM : x j = (M : ℤ) := by
          by_contra hcon
          refine hxa fun l => ?_
          rw [loCoord_two_mul, hiCoord_two_mul]
          by_cases hl : l = j
          · rw [hl, add_unit_self]
            have h := hx j
            rw [loCoord_two_mul, hiCoord_two_mul] at h
            omega
          · rw [add_unit_other _ _ _ _ hl]
            have h := hx l
            rw [loCoord_two_mul, hiCoord_two_mul] at h
            omega
        rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hxa, hxjM, sub_zero]
        exact le_trans (odo_le_corner d M hd c hc0 hc1 (n + 1) x hx j hxjM) (hcor (n + 1))
    · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hx]
      have h1 := odo_nonneg d (2 * M) (fun _ => c) (n + 1) (x + unit j)
      have h2 : (0 : ℤ) ≤ (k : ℤ) * x j := mul_nonneg (by omega) (by omega)
      omega

end Derivative

end DimRed
