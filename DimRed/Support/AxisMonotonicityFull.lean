module

public import DimRed.Support.AxisStep

@[expose] public section

/-!
# Axis monotonicity for arbitrary constant integer heights

The two mirror geometries from `AxisStep` apply directly to the physical
threshold recurrence. A strict old inequality survives a single firing.
At equality, compare all directed neighbor occurrences and then the firing
indicators; this uses no bound on the initial height.
-/

namespace DimRed.Corrected

open LatticeProb

/-- Axis monotonicity across a reflection mirror: a step away from the mirror
`u_i = 1/2` does not increase the odometer. -/
theorem odo_axis_refl (d M : ℕ) (c : ℤ) :
    ∀ (t : ℕ) (u : Site d) (i : Fin d), 1 ≤ u i →
      odo d (2 * M) (fun _ => c) t (u + unit i) ≤ odo d (2 * M) (fun _ => c) t u := by
  intro t
  induction t with
  | zero => intro u i _; simp [odo]
  | succ n ih =>
    intro u i hui
    by_cases hb : inCube d (2 * M) u
    · by_cases ha : inCube d (2 * M) (u + unit i)
      · rcases lt_or_eq_of_le (ih u i hui) with hlt | heq
        · have h1 := (odo_succ_sub_bounds d (2 * M) (fun _ => c) n (u + unit i)).2
          have h2 := odo_mono d (2 * M) (fun _ => c) (show n ≤ n + 1 by omega) u
          omega
        · have hnb : nbrSum (odo d (2 * M) (fun _ => c) n) (u + unit i)
              ≤ nbrSum (odo d (2 * M) (fun _ => c) n) u := by
            refine Finset.sum_le_sum ?_
            intro k _
            have hplus : odo d (2 * M) (fun _ => c) n (u + unit i + unit k)
                ≤ odo d (2 * M) (fun _ => c) n (u + unit k) := by
              have e : u + unit i + unit k = (u + unit k) + unit i := by abel
              rw [e]
              refine ih (u + unit k) i ?_
              rw [add_unit_apply]
              split <;> omega
            have hminus : odo d (2 * M) (fun _ => c) n (u + unit i - unit k)
                ≤ odo d (2 * M) (fun _ => c) n (u - unit k) := by
              have e : u + unit i - unit k = (u - unit k) + unit i := by abel
              rw [e]
              by_cases hki : k = i
              · subst hki
                have e2 : (u - unit k) + unit k = u := by abel
                rw [e2]
                by_cases h2 : 2 ≤ u k
                · have key := ih (u - unit k) k (by rw [sub_unit_apply]; simp; omega)
                  rw [e2] at key
                  exact key
                · have hu1 : u k = 1 := by omega
                  have hrefl := odo_reflect_coord d M c n (u - unit k) k
                  have e3 : (fun l => if l = k then 1 - (u - unit k) k else (u - unit k) l) = u := by
                    funext l
                    by_cases hlk : l = k
                    · subst hlk; rw [ite_eq_left rfl, sub_unit_apply]; simp [hu1]
                    · rw [ite_eq_right hlk, sub_unit_apply]; simp [hlk]
                  rw [e3] at hrefl
                  exact le_of_eq hrefl
              · refine ih (u - unit k) i ?_
                rw [sub_unit_apply]
                simp only [ite_eq_right (fun h : i = k => hki h.symm)]
                omega
            linarith
          have hs : sandp d (2 * M) (fun _ => c) n (u + unit i)
              ≤ sandp d (2 * M) (fun _ => c) n u := by
            simp only [sandp, lap, heq]
            exact add_le_add (le_refl c) (add_le_add (le_refl _) hnb)
          rw [odo_succ_eq d (2 * M) (fun _ => c) n _ ha,
            odo_succ_eq d (2 * M) (fun _ => c) n _ hb, heq]
          split_ifs <;> omega
      · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha]
        exact odo_nonneg d (2 * M) (fun _ => c) (n + 1) u
    · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _
        (not_inCube_add_unit d M u i hui hb),
        odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hb]


/-- Axis monotonicity across a rotation mirror: a step away from the mirror
`u_i = u_j` does not increase the odometer. -/
theorem odo_axis_rot (d M : ℕ) (c : ℤ) :
    ∀ (t : ℕ) (u : Site d) (i j : Fin d), u j ≤ u i →
      odo d (2 * M) (fun _ => c) t (u + unit i - unit j)
        ≤ odo d (2 * M) (fun _ => c) t u := by
  intro t
  induction t with
  | zero => intro u i j _; simp [odo]
  | succ n ih =>
    intro u i j hu
    by_cases hij : i = j
    · subst hij
      have e : u + unit i - unit i = u := by abel
      rw [e]
    · by_cases hb : inCube d (2 * M) u
      · by_cases ha : inCube d (2 * M) (u + unit i - unit j)
        · rcases lt_or_eq_of_le (ih u i j hu) with hlt | heq
          · have h1 := (odo_succ_sub_bounds d (2 * M) (fun _ => c) n
              (u + unit i - unit j)).2
            have h2 := odo_mono d (2 * M) (fun _ => c) (show n ≤ n + 1 by omega) u
            omega
          · have hnb : nbrSum (odo d (2 * M) (fun _ => c) n) (u + unit i - unit j)
                ≤ nbrSum (odo d (2 * M) (fun _ => c) n) u := by
              refine Finset.sum_le_sum ?_
              intro k _
              have hplus : odo d (2 * M) (fun _ => c) n (u + unit i - unit j + unit k)
                  ≤ odo d (2 * M) (fun _ => c) n (u + unit k) := by
                by_cases hkj : k = j
                · subst hkj
                  have e : u + unit i - unit k + unit k = u + unit i := by abel
                  rw [e]
                  by_cases hlt : u k + 1 ≤ u i
                  · have e2 : u + unit i = (u + unit k) + unit i - unit k := by abel
                    rw [e2]
                    refine ih (u + unit k) i k ?_
                    rw [add_unit_self, add_unit_other d u k i hij]
                    omega
                  · have he : u i = u k := le_antisymm (by omega) hu
                    exact le_of_eq (odo_swap_add d M c n u i k hij he)
                · have e : u + unit i - unit j + unit k = (u + unit k) + unit i - unit j := by
                    abel
                  rw [e]
                  refine ih (u + unit k) i j ?_
                  rw [add_unit_other d u k j (fun h : j = k => hkj h.symm), add_unit_apply]
                  split <;> omega
              have hminus : odo d (2 * M) (fun _ => c) n (u + unit i - unit j - unit k)
                  ≤ odo d (2 * M) (fun _ => c) n (u - unit k) := by
                by_cases hki : k = i
                · subst hki
                  have e : u + unit k - unit j - unit k = u - unit j := by abel
                  rw [e]
                  by_cases hlt : u j < u k
                  · have e2 : u - unit j = (u - unit k) + unit k - unit j := by abel
                    rw [e2]
                    refine ih (u - unit k) k j ?_
                    rw [sub_unit_self, sub_unit_other d u k j (Ne.symm hij)]
                    omega
                  · have he : u k = u j := le_antisymm (by omega) hu
                    exact le_of_eq (odo_swap_sub d M c n u k j hij he)
                · have e : u + unit i - unit j - unit k = (u - unit k) + unit i - unit j := by
                    abel
                  rw [e]
                  refine ih (u - unit k) i j ?_
                  rw [sub_unit_other d u k i (fun h : i = k => hki h.symm), sub_unit_apply]
                  split <;> omega
              linarith
            have hs : sandp d (2 * M) (fun _ => c) n (u + unit i - unit j)
                ≤ sandp d (2 * M) (fun _ => c) n u := by
              simp only [sandp, lap, heq]
              exact add_le_add (le_refl c) (add_le_add (le_refl _) hnb)
            rw [odo_succ_eq d (2 * M) (fun _ => c) n _ ha,
              odo_succ_eq d (2 * M) (fun _ => c) n _ hb, heq]
            split_ifs <;> omega
        · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha]
          exact odo_nonneg d (2 * M) (fun _ => c) (n + 1) u
      · have ha : ¬ inCube d (2 * M) (u + unit i - unit j) := fun hc =>
          hb (inCube_of_rot d M u i j hij hu hc)
        rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha,
          odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hb]


/-- Elementary axis monotonicity on the sorted fundamental domain, for every
constant integer initial height. The two moves are `eᵢ` and `eᵢ - eⱼ`, `i < j`. -/
theorem axis_monotonicity (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (t : ℕ) (_ht : 1 ≤ t) (x : Site d) (hx : inSimplex d M x)
    (i : Fin d) (J : Finset (Fin d)) (hJ : J.card ≤ 1) (hiJ : ∀ j ∈ J, i < j)
    (hmem : inSimplex d M (x + unit i - ∑ j ∈ J, unit j)) :
    odo d (2 * M) (fun _ => c) t (x + unit i - ∑ j ∈ J, unit j)
      ≤ odo d (2 * M) (fun _ => c) t x := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h := hmem.1 ⟨0, lt_of_lt_of_le Nat.zero_lt_one hd⟩
    omega
  · rcases Nat.lt_or_ge J.card 1 with h0 | h1
    · have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      simp only [Finset.sum_empty, sub_zero]
      exact odo_axis_refl d M c t x i (hx.1 i).1
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (le_antisymm hJ h1)
      subst hj
      simp only [Finset.sum_singleton]
      exact odo_axis_rot d M c t x i j
        (hx.2 i j (le_of_lt (hiJ j (Finset.mem_singleton_self j))))

end DimRed.Corrected

/-! ## Acceptance examples

Applications of `axis_monotonicity` at a negative height, the critical height `2d`, and a height
above `4d - 1`, for both axis families. -/

open LatticeProb DimRed


-- Signed, critical, and high-height applications of the exact requested type.
example :
    odo 1 4 (fun _ => (-1 : ℤ)) 3 ((fun _ => 1) + unit (0 : Fin 1))
      ≤ odo 1 4 (fun _ => (-1 : ℤ)) 3 (fun _ => 1) := by
  simpa only [Finset.sum_empty, sub_zero] using
    (DimRed.Corrected.axis_monotonicity 1 2 (by decide) (-1) 3 (by decide)
      (fun _ => 1) (by decide) 0 ∅ (by decide) (by simp) (by decide))

example :
    odo 1 4 (fun _ => (2 : ℤ)) 3 ((fun _ => 1) + unit (0 : Fin 1))
      ≤ odo 1 4 (fun _ => (2 : ℤ)) 3 (fun _ => 1) := by
  simpa only [Finset.sum_empty, sub_zero] using
    (DimRed.Corrected.axis_monotonicity 1 2 (by decide) 2 3 (by decide)
      (fun _ => 1) (by decide) 0 ∅ (by decide) (by simp) (by decide))

example :
    odo 1 4 (fun _ => (5 : ℤ)) 3 ((fun _ => 1) + unit (0 : Fin 1))
      ≤ odo 1 4 (fun _ => (5 : ℤ)) 3 (fun _ => 1) := by
  simpa only [Finset.sum_empty, sub_zero] using
    (DimRed.Corrected.axis_monotonicity 1 2 (by decide) 5 3 (by decide)
      (fun _ => 1) (by decide) 0 ∅ (by decide) (by simp) (by decide))

example :
    odo 2 6 (fun _ => (-1 : ℤ)) 3 ((fun _ => 2) + unit (0 : Fin 2) - unit 1)
      ≤ odo 2 6 (fun _ => (-1 : ℤ)) 3 (fun _ => 2) := by
  simpa only [Finset.sum_singleton] using
    (DimRed.Corrected.axis_monotonicity 2 3 (by decide) (-1) 3 (by decide)
      (fun _ => 2) (by decide) 0 {1} (by decide)
      (by intro j hj; rw [Finset.mem_singleton] at hj; subst j; decide)
      (by decide))

example :
    odo 2 6 (fun _ => (4 : ℤ)) 3 ((fun _ => 2) + unit (0 : Fin 2) - unit 1)
      ≤ odo 2 6 (fun _ => (4 : ℤ)) 3 (fun _ => 2) := by
  simpa only [Finset.sum_singleton] using
    (DimRed.Corrected.axis_monotonicity 2 3 (by decide) 4 3 (by decide)
      (fun _ => 2) (by decide) 0 {1} (by decide)
      (by intro j hj; rw [Finset.mem_singleton] at hj; subst j; decide)
      (by decide))

example :
    odo 2 6 (fun _ => (8 : ℤ)) 3 ((fun _ => 2) + unit (0 : Fin 2) - unit 1)
      ≤ odo 2 6 (fun _ => (8 : ℤ)) 3 (fun _ => 2) := by
  simpa only [Finset.sum_singleton] using
    (DimRed.Corrected.axis_monotonicity 2 3 (by decide) 8 3 (by decide)
      (fun _ => 2) (by decide) 0 {1} (by decide)
      (by intro j hj; rw [Finset.mem_singleton] at hj; subst j; decide)
      (by decide))

-- Actual odometer values, checked by kernel reduction (no native evaluation).
example : odo 1 4 (fun _ => (-1 : ℤ)) 3 (fun _ => 1) = 0 := by decide
example : odo 1 4 (fun _ => (2 : ℤ)) 3 (fun _ => 1) = 2 := by decide
example : odo 1 4 (fun _ => (2 : ℤ)) 3 (fun _ => 2) = 2 := by decide
example : odo 1 4 (fun _ => (2 : ℤ)) 2 (fun _ => 1) = 2 := by decide
example : odo 1 4 (fun _ => (2 : ℤ)) 2 (fun _ => 2) = 1 := by decide
example : odo 1 4 (fun _ => (5 : ℤ)) 3 (fun _ => 1) = 3 := by decide
example : odo 1 4 (fun _ => (5 : ℤ)) 3 (fun _ => 2) = 3 := by decide

-- Selected negative reflection: the occurrences at coordinates zero and one agree.
example (c : ℤ) (t : ℕ) :
    odo 1 4 (fun _ => c) t (fun _ => 0) = odo 1 4 (fun _ => c) t (fun _ => 1) := by
  have h := odo_reflect_coord 1 2 c t (fun _ => 0) 0
  have e : (fun k : Fin 1 => if k = 0 then 1 - (0 : ℤ) else 0) = fun _ => (1 : ℤ) := by
    funext k
    fin_cases k
    rfl
  rw [e] at h
  exact h.symm

-- Selected rotation mirror: the exceptional positive pair are swapped images.
example (c : ℤ) (t : ℕ) :
    odo 2 6 (fun _ => c) t ((fun _ => 2) + unit (0 : Fin 2))
      = odo 2 6 (fun _ => c) t ((fun _ => 2) + unit 1) :=
  odo_swap_add 2 3 c t (fun _ => 2) 0 1 (by decide) rfl

-- Scale-one reflection sink and its unrestricted monotonicity application.
example (c : ℤ) (t : ℕ) :
    odo 1 2 (fun _ => c) t ((fun _ => 1) + unit (0 : Fin 1)) = 0 ∧
    odo 1 2 (fun _ => c) t ((fun _ => 1) + unit (0 : Fin 1))
      ≤ odo 1 2 (fun _ => c) t (fun _ => 1) := by
  exact ⟨odo_eq_zero_outside 1 2 _ t _ (by decide),
    DimRed.Corrected.odo_axis_refl 1 1 c t (fun _ => 1) 0 (by decide)⟩

-- Scale-one rotation sink: both directed selected faces are handled.
example (c : ℤ) (t : ℕ) :
    odo 2 2 (fun _ => c) t ((fun _ => 1) + unit (0 : Fin 2) - unit 1) = 0 ∧
    odo 2 2 (fun _ => c) t ((fun _ => 1) + unit (0 : Fin 2) - unit 1)
      ≤ odo 2 2 (fun _ => c) t (fun _ => 1) := by
  exact ⟨odo_eq_zero_outside 2 2 _ t _ (by decide),
    DimRed.Corrected.odo_axis_rot 2 1 c t (fun _ => 1) 0 1 (by decide)⟩

-- A starting site already outside the physical cube remains a sink.
example (c : ℤ) (t : ℕ) :
    odo 1 4 (fun _ => c) t ((fun _ => 3) + unit (0 : Fin 1)) = 0 ∧
    odo 1 4 (fun _ => c) t ((fun _ => 3) + unit (0 : Fin 1))
      ≤ odo 1 4 (fun _ => c) t (fun _ => 3) := by
  exact ⟨odo_eq_zero_outside 1 4 _ t _ (by decide),
    DimRed.Corrected.odo_axis_refl 1 2 c t (fun _ => 3) 0 (by decide)⟩

-- An elementary legal rotation, followed by a legal reflection, composes.
example (c : ℤ) (t : ℕ) :
    odo 2 8 (fun _ => c) t (((fun _ => 2) + unit (0 : Fin 2) - unit 1) + unit 0)
      ≤ odo 2 8 (fun _ => c) t (fun _ => 2) := by
  exact le_trans
    (DimRed.Corrected.odo_axis_refl 2 4 c t _ 0 (by decide))
    (DimRed.Corrected.odo_axis_rot 2 4 c t (fun _ => 2) 0 1 (by decide))

-- CE-MIXED's two negative indices cannot inhabit the target's cardinality premise.
example : ¬ ({1, 2} : Finset (Fin 3)).card ≤ 1 := by decide

-- A scale-one shifted point is deliberately outside the public simplex domain.
example : ¬ inSimplex 1 1 ((fun _ => 1) + unit (0 : Fin 1)) := by decide

-- A high-height example with a strict, active inequality after several firings.
example : odo 1 4 (fun _ => (5 : ℤ)) 5 (fun _ => 1) = 5 := by decide
example : odo 1 4 (fun _ => (5 : ℤ)) 5 (fun _ => 2) = 4 := by decide
