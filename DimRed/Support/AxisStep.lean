module

/-
Axis monotonicity for the parallel toppling odometer of a constant initial
sandpile, in the form of the source Corollary 2.1 cites: the odometer does not
increase along a single step perpendicular to a single axis of symmetry of the
hypercube, away from that axis.

The hypercube `C_{2M}^{(d)}` has two families of mirrors meeting `S_M^{(d)}`:
the reflections `u_i = 1/2`, whose perpendicular step is `e_i`, and the
rotations `u_i = u_j`, whose perpendicular step is `e_i - e_j`.  `odo_axis_refl`
and `odo_axis_rot` are the two monotonicity statements, each proved by the
induction of Babai and Gorodezky's Lemma 5.3: the odometer gains at most one per
step, so the only case to treat is a site whose value has caught up, and there
the recursion of the statement labelled `pt_ind_lemma` in `dimred-corrected-arxiv.tex` compares the two neighbour sums term by
term.  A term where the step would leave the mirror on the wrong side is the
site's own mirror image, and the two terms are equal.
-/
public import DimRed.Support.Fundamental
public import DimRed.Support.Stabilize
public import DimRed.Support.NonnegativeUpdate

@[expose] public section

namespace DimRed

open LatticeProb

variable {d : ℕ}

section Symmetry

/-- A constant initial sandpile is symmetric. -/
theorem isSymmetricPile_const' (d N : ℕ) (c : ℤ) :
    IsSymmetricPile d N (fun _ => c) := fun _ _ _ => rfl

/-- Reflecting the `i`-th coordinate in the mirror `u_i = 1/2` fixes the
odometer of a constant initial sandpile. -/
theorem odo_reflect_coord (d M : ℕ) (c : ℤ) (t : ℕ) (u : Site d) (i : Fin d) :
    odo d (2 * M) (fun _ => c) t (fun k => if k = i then 1 - u i else u k)
      = odo d (2 * M) (fun _ => c) t u := by
  have h := odo_cubeSym d (2 * M) (fun _ => c) (isSymmetricPile_const' d (2 * M) c) t
    (Equiv.refl (Fin d)) (fun k => decide (k ≠ i)) u
  have e : cubeSym d (2 * M) (Equiv.refl (Fin d)) (fun k => decide (k ≠ i)) u
      = fun k => if k = i then 1 - u i else u k := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [cubeSym, loCoord_two_mul, hiCoord_two_mul]
    · simp [cubeSym, hk]
  rwa [e] at h

/-- Swapping two coordinates fixes the odometer of a constant initial
sandpile. -/
theorem odo_swap_coord (d M : ℕ) (c : ℤ) (t : ℕ) (u : Site d) (i j : Fin d) :
    odo d (2 * M) (fun _ => c) t (fun k => u (Equiv.swap i j k))
      = odo d (2 * M) (fun _ => c) t u := by
  have h := odo_cubeSym d (2 * M) (fun _ => c) (isSymmetricPile_const' d (2 * M) c) t
    (Equiv.swap i j) (fun _ => true) u
  have e : cubeSym d (2 * M) (Equiv.swap i j) (fun _ => true) u
      = fun k => u (Equiv.swap i j k) := by
    funext k; simp [cubeSym]
  rwa [e] at h

end Symmetry

section Steps

variable (d M : ℕ)

/-- `(u + unit i) k = u k + 1` at `k = i` and `u k` elsewhere. -/
theorem add_unit_apply (u : Site d) (i k : Fin d) :
    (u + unit i) k = u k + (if k = i then 1 else 0) := by
  simp [unit, Pi.single_apply]

theorem sub_unit_apply (u : Site d) (i k : Fin d) :
    (u - unit i) k = u k - (if k = i then 1 else 0) := by
  simp [unit, Pi.single_apply]

theorem add_unit_self (u : Site d) (i : Fin d) : (u + unit i) i = u i + 1 := by
  rw [add_unit_apply]; simp

theorem add_unit_other (u : Site d) (i k : Fin d) (h : k ≠ i) : (u + unit i) k = u k := by
  rw [add_unit_apply, if_neg h]; ring

theorem sub_unit_self (u : Site d) (i : Fin d) : (u - unit i) i = u i - 1 := by
  rw [sub_unit_apply]; simp

theorem sub_unit_other (u : Site d) (i k : Fin d) (h : k ≠ i) : (u - unit i) k = u k := by
  rw [sub_unit_apply, if_neg h]; ring

end Steps

section Reflection

variable (d M : ℕ)

/-- A site outside the hypercube stays outside after a step away from the
mirror `u_i = 1/2`. -/
theorem not_inCube_add_unit (u : Site d) (i : Fin d) (hui : 1 ≤ u i)
    (h : ¬ inCube d (2 * M) u) : ¬ inCube d (2 * M) (u + unit i) := by
  have hM : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
  intro hc
  refine h fun k => ?_
  have hk := hc k
  rw [add_unit_apply, loCoord_two_mul, hiCoord_two_mul] at hk
  rw [loCoord_two_mul, hiCoord_two_mul]
  split_ifs at hk with h1
  · subst h1; omega
  · omega

/-- Axis monotonicity across a reflection mirror: a step away from the mirror
`u_i = 1/2` does not increase the odometer. -/
theorem odo_axis_refl (hd : 1 ≤ d) (c : ℤ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) :
    ∀ (t : ℕ) (u : Site d) (i : Fin d), 1 ≤ u i →
      odo d (2 * M) (fun _ => c) t (u + unit i) ≤ odo d (2 * M) (fun _ => c) t u := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
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
        · rw [DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ ha,
            DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ hb]
          refine Int.ediv_le_ediv hdpos ?_
          have hnb : nbrSum (odo d (2 * M) (fun _ => c) n) (u + unit i)
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
                    · subst hlk; rw [if_pos rfl, sub_unit_apply]; simp [hu1]
                    · rw [if_neg hlk, sub_unit_apply]; simp [hlk]
                  rw [e3] at hrefl
                  exact le_of_eq hrefl
              · refine ih (u - unit k) i ?_
                rw [sub_unit_apply]
                simp only [if_neg (fun h : i = k => hki h.symm)]
                omega
            linarith
          linarith
      · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha]
        exact odo_nonneg d (2 * M) (fun _ => c) (n + 1) u
    · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _
        (not_inCube_add_unit d M u i hui hb),
        odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hb]

end Reflection

section Rotation

variable (d M : ℕ)

theorem rot_apply (u : Site d) (i j k : Fin d) :
    (u + unit i - unit j) k
      = u k + (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
  simp [unit, Pi.single_apply]

/-- On the rotation mirror `u_i = u_j` the two steps `u + e_i` and `u + e_j` are
mirror images, so the odometer takes the same value at both. -/
theorem odo_swap_add (c : ℤ) (t : ℕ) (u : Site d) (i j : Fin d)
    (hij : i ≠ j) (he : u i = u j) :
    odo d (2 * M) (fun _ => c) t (u + unit i)
      = odo d (2 * M) (fun _ => c) t (u + unit j) := by
  have h := odo_swap_coord d M c t (u + unit j) i j
  have e : (fun l => (u + unit j) (Equiv.swap i j l)) = u + unit i := by
    funext l
    by_cases hli : l = i
    · subst hli
      rw [Equiv.swap_apply_left, add_unit_self, add_unit_self, he]
    · by_cases hlj : l = j
      · subst hlj
        rw [Equiv.swap_apply_right, add_unit_other d u l i hij,
          add_unit_other d u i l (Ne.symm hij)]
        exact he
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj, add_unit_other d u j l hlj,
          add_unit_other d u i l hli]
  rwa [e] at h

/-- The same for the two steps `u - e_i` and `u - e_j`. -/
theorem odo_swap_sub (c : ℤ) (t : ℕ) (u : Site d) (i j : Fin d)
    (hij : i ≠ j) (he : u i = u j) :
    odo d (2 * M) (fun _ => c) t (u - unit j)
      = odo d (2 * M) (fun _ => c) t (u - unit i) := by
  have h := odo_swap_coord d M c t (u - unit i) i j
  have e : (fun l => (u - unit i) (Equiv.swap i j l)) = u - unit j := by
    funext l
    by_cases hli : l = i
    · subst hli
      rw [Equiv.swap_apply_left, sub_unit_other d u l j (Ne.symm hij),
        sub_unit_other d u j l hij, he]
    · by_cases hlj : l = j
      · subst hlj
        rw [Equiv.swap_apply_right, sub_unit_self, sub_unit_self, he]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj, sub_unit_other d u i l hli,
          sub_unit_other d u j l hlj]
  rwa [e] at h

/-- A site whose rotation step lands in the hypercube was in it to begin with. -/
theorem inCube_of_rot (u : Site d) (i j : Fin d) (hij : i ≠ j) (hu : u j ≤ u i)
    (hc : inCube d (2 * M) (u + unit i - unit j)) : inCube d (2 * M) u := by
  have hM : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
  have hi : 1 - (M : ℤ) ≤ u i + 1 ∧ u i + 1 ≤ (M : ℤ) := by
    have h := hc i
    rw [rot_apply, loCoord_two_mul, hiCoord_two_mul, if_pos rfl, if_neg hij] at h
    simpa using h
  have hj : 1 - (M : ℤ) ≤ u j - 1 ∧ u j - 1 ≤ (M : ℤ) := by
    have h := hc j
    rw [rot_apply, loCoord_two_mul, hiCoord_two_mul, if_neg (Ne.symm hij), if_pos rfl] at h
    simpa using h
  intro k
  rw [loCoord_two_mul, hiCoord_two_mul]
  by_cases hki : k = i
  · subst hki; omega
  · by_cases hkj : k = j
    · subst hkj; omega
    · have h := hc k
      rw [rot_apply, loCoord_two_mul, hiCoord_two_mul, if_neg hki, if_neg hkj] at h
      simpa using h

/-- Axis monotonicity across a rotation mirror: a step away from the mirror
`u_i = u_j` does not increase the odometer. -/
theorem odo_axis_rot (hd : 1 ≤ d) (c : ℤ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1) :
    ∀ (t : ℕ) (u : Site d) (i j : Fin d), u j ≤ u i →
      odo d (2 * M) (fun _ => c) t (u + unit i - unit j)
        ≤ odo d (2 * M) (fun _ => c) t u := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
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
          · rw [DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ ha,
              DimRed.bounded_point_update d (2 * M) hd _ (fun _ _ => hc0) (fun _ _ => hc1) n _ hb]
            refine Int.ediv_le_ediv hdpos ?_
            have hnb : nbrSum (odo d (2 * M) (fun _ => c) n) (u + unit i - unit j)
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
            linarith
        · rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha]
          exact odo_nonneg d (2 * M) (fun _ => c) (n + 1) u
      · have ha : ¬ inCube d (2 * M) (u + unit i - unit j) := fun hc =>
          hb (inCube_of_rot d M u i j hij hu hc)
        rw [odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ ha,
          odo_eq_zero_outside d (2 * M) (fun _ => c) (n + 1) _ hb]

end Rotation

end DimRed
