module

public import DimRed.Support.AxisMonotonicityFull
public import DimRed.Support.DerivBound
public import DimRed.Support.Case2QuadraticBarrier

@[expose] public section

/-!
# Constant-height derivative bound with a terminal corner cap

The proof uses the physical threshold update at arbitrary integer initial heights.
Unrestricted reflection monotonicity bounds every top face by the corner. At a
saturated first difference, summing all directed affine weights compares the two
sandpile heights and hence their firing indicators.
-/

namespace DimRed.Corrected

open LatticeProb

-- Walking down positive coordinates uses unrestricted reflection monotonicity;
-- the intermediate points need not be sorted.
private theorem odo_le_of_positive_le (d M : ℕ) (c : ℤ) (t : ℕ) :
    ∀ (n : ℕ) (x y : Site d), (∀ i, 1 ≤ y i) → (∀ i, y i ≤ x i) →
      (∑ i, (x i - y i)).toNat = n →
      odo d (2 * M) (fun _ => c) t x ≤ odo d (2 * M) (fun _ => c) t y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hy hle hn
    by_cases heq : ∀ i, x i = y i
    · rw [funext heq]
    · obtain ⟨i, hi⟩ := not_forall.mp heq
      have hilt : y i < x i := lt_of_le_of_ne (hle i) (Ne.symm hi)
      set z : Site d := x - unit i with hz
      have hzi : z i = x i - 1 := by rw [hz, sub_unit_self]
      have hzl : ∀ l, l ≠ i → z l = x l := fun l hl => by
        rw [hz, sub_unit_other d x i l hl]
      have hzy : ∀ l, y l ≤ z l := by
        intro l
        by_cases hl : l = i
        · rw [hl, hzi]; omega
        · rw [hzl l hl]; exact hle l
      have hstep : odo d (2 * M) (fun _ => c) t x
          ≤ odo d (2 * M) (fun _ => c) t z := by
        have e : z + unit i = x := by rw [hz]; abel
        have h := odo_axis_refl d M c t z i (by have := hy i; rw [hzi]; omega)
        rwa [e] at h
      have hkey : ∀ l, z l - y l = (x l - y l) - (if l = i then 1 else 0) := by
        intro l
        by_cases hl : l = i
        · rw [hl, hzi, ite_eq_left rfl]; ring
        · rw [hzl l hl, ite_eq_right hl]; ring
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
        (ih ((∑ l, (z l - y l)).toNat) (by omega) z y hy hzy rfl)

private theorem odo_le_corner (d M : ℕ) (hd : 1 ≤ d) (c : ℤ) (t : ℕ)
    (x : Site d) (hx : inCube d (2 * M) x)
    (j : Fin d) (hxj : x j = (M : ℤ)) :
    odo d (2 * M) (fun _ => c) t x
      ≤ odo d (2 * M) (fun _ => c) t (cornerPoint d M) := by
  classical
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    have h := hx j
    rw [loCoord_two_mul, hiCoord_two_mul] at h
    omega
  set y := toSimplexPoint d M x with hy
  have hyS : inSimplex d M y := inSimplex_toSimplexPoint d M x hx
  have hyx : odo d (2 * M) (fun _ => c) t y = odo d (2 * M) (fun _ => c) t x :=
    odo_toSimplexPoint d M (fun _ => c) (isSymmetricPile_const' d (2 * M) c) t x
  -- `M` occurs among the folded coordinates, so the largest coordinate of `y` is `M`
  have hzero : (0 : ℕ) < d := hd
  set i0 : Fin d := ⟨0, hzero⟩ with hi0
  have hfold : foldPoint d (2 * M) x j = (M : ℤ) := by
    rw [foldPoint_apply, ite_eq_left (by omega : (1 : ℤ) ≤ x j), hxj]
  obtain ⟨m, hm⟩ := (Tuple.sort (fun i => -(foldPoint d (2 * M) x i))).surjective j
  have hym : y m = (M : ℤ) := by rw [hy, toSimplexPoint, hm, hfold]
  have hy0 : (M : ℤ) ≤ y i0 := by
    rw [← hym]
    exact hyS.2 i0 m (Fin.le_def.mpr (by simp [hi0]))
  have hle : ∀ l, cornerPoint d M l ≤ y l := by
    intro l
    rw [cornerPoint]
    by_cases hl : (l : ℕ) = 0
    · rw [ite_eq_left hl]
      have : l = i0 := by ext; simpa [hi0] using hl
      rw [this]; exact hy0
    · rw [ite_eq_right hl]; exact (hyS.1 l).1
  rw [← hyx]
  exact odo_le_of_positive_le d M c t _ y (cornerPoint d M)
    (by intro l; rw [cornerPoint]; split <;> omega) hle rfl

private theorem odo_deriv_bound (d M : ℕ) (hd : 1 ≤ d) (c : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hcor : ∀ t, odo d (2 * M) (fun _ => c) t (cornerPoint d M) ≤ (k : ℤ) * (M : ℤ)) :
    ∀ (t : ℕ) (j : Fin d) (x : Site d), 1 ≤ x j →
      odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + unit j)
        ≤ (k : ℤ) * x j := by
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
          have hs : sandp d (2 * M) (fun _ => c) n x
              ≤ sandp d (2 * M) (fun _ => c) n (x + unit j) := by
            simp only [sandp, lap]
            nlinarith [hAB, heq]
          rw [odo_succ_eq d (2 * M) (fun _ => c) n x hx,
            odo_succ_eq d (2 * M) (fun _ => c) n (x + unit j) hxa]
          split_ifs <;> omega
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
        exact le_trans (odo_le_corner d M hd c (n + 1) x hx j hxjM) (hcor (n + 1))
    · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hx]
      have h1 := odo_nonneg d (2 * M) (fun _ => c) (n + 1) (x + unit j)
      have h2 : (0 : ℤ) ≤ (k : ℤ) * x j := mul_nonneg (by omega) (by omega)
      omega

/-- A genuine terminal corner cap bounds every coordinate first difference,
for every constant integer initial height. -/
theorem derivative_bound (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (k : ℕ) (hk : 1 ≤ k)
    (hcorner : odoInf d (2 * M) (fun _ => c) (cornerPoint d M) ≤ ((k * M : ℕ) : ℕ∞))
    (j : Fin d) (t : ℕ) (x : Site d) (hx : inSimplex d M x) :
    odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + unit j)
      ≤ (k : ℤ) * x j := by
  have hcor : ∀ s : ℕ,
      odo d (2 * M) (fun _ => c) s (cornerPoint d M) ≤ (k : ℤ) * (M : ℤ) := by
    intro s
    have hle : ((odo d (2 * M) (fun _ => c) s (cornerPoint d M)).toNat : ℕ∞)
        ≤ ((k * M : ℕ) : ℕ∞) :=
      le_trans (le_iSup
        (fun n : ℕ => ((odo d (2 * M) (fun _ => c) n (cornerPoint d M)).toNat : ℕ∞)) s)
        hcorner
    have hle' : (odo d (2 * M) (fun _ => c) s (cornerPoint d M)).toNat ≤ k * M :=
      ENat.natCast_le_natCast.mp hle
    have hz := Int.toNat_le.mp hle'
    push_cast at hz
    exact hz
  exact odo_deriv_bound d M hd c k hk hcor t j x (hx.1 j).1

/-! ## Acceptance applications -/

-- The quadratic barrier produces the premise, rather than assuming a cap.
private theorem uniform_corner_cap (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    odoInf d (2 * M) (fun _ => 2 * (d : ℤ)) (cornerPoint d M) ≤ (M : ℕ∞) := by
  have hM' : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  let i : Fin d := ⟨0, hd⟩
  have hx : inCube d (2 * M) (cornerPoint d M) := by
    intro l
    rw [loCoord_two_mul, hiCoord_two_mul, cornerPoint]
    split <;> omega
  have hxi : cornerPoint d M i = (M : ℤ) := by simp [cornerPoint, i]
  apply iSup_le
  intro t
  have h := case2_odo_le_M_at_face d M t hd hM i (cornerPoint d M) hx hxi
  exact ENat.natCast_le_natCast.mpr (Int.toNat_le.mpr h)

-- The source's k = 1 first-difference consumer, with its premise proved above.
example (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (j : Fin d) (t : ℕ)
    (x : Site d) (hx : inSimplex d M x) :
    odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit j) ≤ x j := by
  have hcap : odoInf d (2 * M) (fun _ => 2 * (d : ℤ)) (cornerPoint d M)
      ≤ (((1 : ℕ) * M : ℕ) : ℕ∞) := by
    simpa only [Nat.one_mul] using uniform_corner_cap d M hd hM
  simpa only [odoUnif, Nat.cast_one, one_mul] using
    derivative_bound d M hd (2 * (d : ℤ)) 1 (by omega) hcap j t x hx

-- An active, nonzero corner cap: v_∞(2) = 2 and the face difference is 2.
example : odoInf 1 4 (fun _ => (2 : ℤ)) (cornerPoint 1 2) = (2 : ℕ∞) ∧
    odo 1 4 (fun _ => (2 : ℤ)) 3 (cornerPoint 1 2) -
      odo 1 4 (fun _ => (2 : ℤ)) 3 (cornerPoint 1 2 + unit (0 : Fin 1)) ≤ 2 := by
  have hcap : odoInf 1 4 (fun _ => (2 : ℤ)) (cornerPoint 1 2) ≤ (2 : ℕ∞) :=
    uniform_corner_cap 1 2 (by decide) (by decide)
  constructor
  · apply le_antisymm hcap
    have hvalue : odo 1 4 (fun _ => (2 : ℤ)) 3 (cornerPoint 1 2) = 2 := by decide
    have hle := le_iSup
      (fun t : ℕ => ((odo 1 4 (fun _ => (2 : ℤ)) t (cornerPoint 1 2)).toNat : ℕ∞)) 3
    simpa [odoInf, hvalue] using hle
  · have h := derivative_bound 1 2 (by decide) 2 1 (by decide)
      (by simpa using hcap) 0 3 (cornerPoint 1 2) (by decide)
    simpa [cornerPoint] using h

example : odo 1 4 (fun _ => (2 : ℤ)) 3 (cornerPoint 1 2) -
    odo 1 4 (fun _ => (2 : ℤ)) 3 (cornerPoint 1 2 + unit (0 : Fin 1)) = 2 := by decide

-- At M = 1 every selected positive neighbor is a sink.
example (t : ℕ) :
    odo 2 2 (fun _ => (4 : ℤ)) t (cornerPoint 2 1) -
      odo 2 2 (fun _ => (4 : ℤ)) t (cornerPoint 2 1 + unit (1 : Fin 2)) ≤ 1 := by
  have hcap := uniform_corner_cap 2 1 (by decide) (by decide)
  have h := derivative_bound 2 1 (by decide) 4 1 (by decide)
    (by simpa using hcap) 1 t (cornerPoint 2 1) (by decide)
  simpa [cornerPoint] using h

-- Signed input: no site fires, and its actual terminal cap is zero.
example (t : ℕ) :
    odo 1 2 (fun _ => (-1 : ℤ)) t (cornerPoint 1 1) -
      odo 1 2 (fun _ => (-1 : ℤ)) t (cornerPoint 1 1 + unit (0 : Fin 1)) ≤ 1 := by
  have hstable : odo 1 2 (fun _ => (-1 : ℤ)) (0 + 1) =
      odo 1 2 (fun _ => (-1 : ℤ)) 0 := by
    funext x
    simp [odo, lap, nbrSum]
  have hzero := odoInf_eq_of_stable 1 2 (fun _ => (-1 : ℤ)) 0 hstable (cornerPoint 1 1)
  have hcap : odoInf 1 2 (fun _ => (-1 : ℤ)) (cornerPoint 1 1)
      ≤ (((1 : ℕ) * 1 : ℕ) : ℕ∞) := by
    rw [hzero]
    decide
  have h := derivative_bound 1 1 (by decide) (-1) 1 (by decide) hcap 0 t
    (cornerPoint 1 1) (by decide)
  simpa [cornerPoint] using h

-- A height above 4d - 1: on C₂ in dimension one, height five stabilizes at v = 4.
private theorem high_height_stable :
    odo 1 2 (fun _ => (5 : ℤ)) (4 + 1) = odo 1 2 (fun _ => (5 : ℤ)) 4 := by
  funext x
  by_cases hx : inCube 1 2 x
  · have hcoord := hx 0
    have hcases : x 0 = 0 ∨ x 0 = 1 := by
      norm_num [loCoord, hiCoord, sideHalf] at hcoord
      omega
    rcases hcases with hzero | hone
    · have he : x = fun _ => (0 : ℤ) := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simpa only [hi] using hzero
      rw [he]
      decide
    · have he : x = fun _ => (1 : ℤ) := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simpa only [hi] using hone
      rw [he]
      decide
  · rw [odo_eq_zero_outside 1 2 _ (4 + 1) x hx, odo_eq_zero_outside 1 2 _ 4 x hx]

example (t : ℕ) : odoInf 1 2 (fun _ => (5 : ℤ)) (cornerPoint 1 1) = (4 : ℕ∞) ∧
    odo 1 2 (fun _ => (5 : ℤ)) t (cornerPoint 1 1) -
      odo 1 2 (fun _ => (5 : ℤ)) t (cornerPoint 1 1 + unit (0 : Fin 1)) ≤ 4 := by
  have hterminal := odoInf_eq_of_stable 1 2 (fun _ => (5 : ℤ)) 4
    high_height_stable (cornerPoint 1 1)
  have hvalue : odo 1 2 (fun _ => (5 : ℤ)) 4 (cornerPoint 1 1) = 4 := by decide
  have heq : odoInf 1 2 (fun _ => (5 : ℤ)) (cornerPoint 1 1) = (4 : ℕ∞) := by
    simpa [hvalue] using hterminal
  refine ⟨heq, ?_⟩
  have hcap : odoInf 1 2 (fun _ => (5 : ℤ)) (cornerPoint 1 1)
      ≤ (((4 : ℕ) * 1 : ℕ) : ℕ∞) := by rw [heq]; decide
  have h := derivative_bound 1 1 (by decide) 5 4 (by decide) hcap 0 t
    (cornerPoint 1 1) (by decide)
  simpa [cornerPoint] using h

end DimRed.Corrected
