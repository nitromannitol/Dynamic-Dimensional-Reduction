import DimRed.Support.RegFacetTime
import DimRed.Support.FacetNbr

/-!
# Strong facet compatibility at one triple

Strong facet compatibility at one triple, `dimred.tex:1261-1320`, by strong
induction on the time.

The paper's argument: suppose `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1`.  By
strong facet compatibility at `(t-1) → t`, `Δ v_{t-1}(x_i, 1, 1_j) ≥ 0`, so it
suffices to compare the two Laplacians term by term.  The terms come from strong
facet compatibility at time `t-1`, which the strong induction on `t` supplies —
this is what removes the apparent circularity of consuming the clause at the same
triple.

The first-difference part of the clause is Corollary 2.2 at the mid coordinate.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the Laplacian comparison expands two `Finset.sum`s over `Fin i` and the
-- `nlinarith` call needs the extra budget
set_option maxHeartbeats 800000

namespace DimRed

open LatticeProb

/-- The three term bounds of the paper's Laplacian comparison
(`dimred.tex:1293-1300`), each supplied by strong facet compatibility at time
`t-1`:

* the head terms at time `t` dominate those at time `t-1` (the paper's
  `eq:laplace_11 ≥ eq:laplace_21`);
* the mid term at time `t-1` is at most the mid term at time `t`
  (`eq:laplace_12 ≥ eq:laplace_22`);
* the tail term at time `t-1` is at most the tail term at time `t`
  (`eq:laplace_13 ≥ eq:laplace_23`). -/
structure FacetTermBounds (i j M t : ℕ) (y : Fin i → ℤ) : Prop where
  head : (∑ a : Fin i,
      (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j) +
        odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j)))
    ≤ (∑ a : Fin i,
      (odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) +
        odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j)))
  mid : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
    = odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j)
  tail : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j)
    ≤ odoUnif (i + 1 + j) (2 * M) t (facetTailRaise y j)
  /-- the gap at time `t-1`, which the clause supplies in the toppling case -/
  gap : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
    = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) + 1
  /-- the two-step bound at time `t`, `eq:two_derivative_bound` -/
  two : odoUnif (i + 1 + j) (2 * M) t (facetPoint y 1 j)
    - odoUnif (i + 1 + j) (2 * M) t (facetPoint y 3 j) ≤ 2

/-- The Laplacian at the facet point `(y, 1, 1_j)` is at most the Laplacian at
`(y, 2, 1_j)` when the clause holds at the previous time and the two-step bound
holds at the current time.  This is the paper's comparison of
`eq:laplace_11`–`eq:laplace_13` with `eq:laplace_21`–`eq:laplace_23`. -/
theorem lap_facet_le_of_prev {i j M t : ℕ} (_ht : 1 ≤ t) (_hi : 1 ≤ i) (_hM : 2 ≤ M)
    (_hS : RegStrongFacet (i + 1 + j) M (t - 1))
    (_hderiv : RegStrongDeriv (i + 1 + j) M t)
    (y : Fin i → ℤ) (_hy2 : ∀ a, 2 ≤ y a)
    (_hys : inSimplex (i + 1 + j) M (facetPoint y 1 j))
    (_hys2 : inSimplex (i + 1 + j) M (facetPoint y 2 j))
    (hb : FacetTermBounds i j M t y)
    (hlap2 : lap (odoUnif (i + 1 + j) (2 * M) t) (facetPoint y 2 j)
      = (∑ a : Fin i,
          (odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) +
            odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j))) -
        2 * (i : ℤ) * odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) +
        ((j : ℤ) + 1) *
          (odoUnif (i + 1 + j) (2 * M) t (facetTailRaise y j) -
            odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j)))
    (_hgap : odoUnif (i + 1 + j) (2 * M) t (facetPoint y 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) + 1) :
    lap (odoUnif (i + 1 + j) (2 * M) (t - 1)) (facetPoint y 1 j)
      ≤ lap (odoUnif (i + 1 + j) (2 * M) t) (facetPoint y 2 j) := by
  -- the two-step bound at the head coordinates
  have htwo := hb.two
  have hhead := hb.head
  -- the mid and tail terms
  have hmid := hb.mid
  have htail := hb.tail
  -- the two Laplacians, in the paper's decomposition
  have hlap1 : lap (odoUnif (i + 1 + j) (2 * M) (t - 1)) (facetPoint y 1 j)
      = (∑ a : Fin i,
          (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j) +
            odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j))) -
        2 * (i : ℤ) * odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j) +
        ((j : ℤ) + 1) *
          (odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) -
            odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)) := by
    have h := lap_facetPoint_of (i := i) (j := j) (M := M)
      (2 * ((i + 1 + j : ℕ) : ℤ)) y (t - 1)
    simp only [odoUnif]
    exact h
  rw [hlap1]
  rw [hlap2]
  -- the head value at `t-1` is the mid value at `t`, and the tail term at `t`
  -- dominates the mid value at `t-1`
  have hj1 : (0 : ℤ) ≤ (j : ℤ) + 1 := by positivity
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  nlinarith [hb.head, hb.mid, hb.tail, hb.gap, hj1, hi0]

/-- The head term of the facet comparison at `y + unit a`, from the time
comparison at the facet normal form of the head neighbour. -/
theorem head_term_add (i j M t : ℕ) (ht : 1 ≤ t) (_hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : ∀ (i' j' : ℕ), i' + 1 + j' = i + 1 + j → 1 ≤ i' →
      RegStrongFacet (i' + 1 + j') M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∀ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) (a : Fin i) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y + unit a) 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint (y + unit a) 2 j) := by
  have hshift : facetPoint (y + unit a) 1 j
      = facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a)) := by
    rw [facetPoint_add_head']
  have hshift2 : facetPoint (y + unit a) 2 j
      = facetPoint y 2 j + unit (Fin.castAdd j (Fin.castSucc a)) := by
    rw [facetPoint_add_head']
  rw [hshift, hshift2]
  by_cases haM : y a = (M : ℤ)
  · -- the point is off the cube: both odometers vanish
    have hoff : ¬ inCube (i + 1 + j) (2 * M)
        (facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a))) := by
      intro hc
      have h := hc (Fin.castAdd j (Fin.castSucc a))
      rw [Pi.add_apply, facetPoint_head, unit_apply_self] at h
      rw [loCoord_two_mul, hiCoord_two_mul] at h
      omega
    have hoff2 : ¬ inCube (i + 1 + j) (2 * M)
        (facetPoint y 2 j + unit (Fin.castAdd j (Fin.castSucc a))) := by
      intro hc
      have h := hc (Fin.castAdd j (Fin.castSucc a))
      rw [Pi.add_apply, facetPoint_head, unit_apply_self] at h
      rw [loCoord_two_mul, hiCoord_two_mul] at h
      omega
    simp only [odoUnif]
    rw [odo_eq_zero_outside _ _ _ _ _ hoff, odo_eq_zero_outside _ _ _ _ _ hoff2]
  -- the head neighbour has its mid coordinate equal to one, so the facet normal
  -- form applies
  have hmid : (facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a)))
      (Fin.castAdd j (Fin.last i)) = 1 := by
    rw [Pi.add_apply, facetPoint_mid]
    have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
        (Fin.castAdd j (Fin.last i)) = 0 := by
      rw [unit_apply_ne]
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
      have hlt := a.isLt
      omega
    rw [hzero, add_zero]
  have hpos : inPos (i + 1 + j) M
      (facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a))) := by
    intro l
    refine Fin.addCases ?_ ?_ l
    · intro h
      refine Fin.lastCases ?_ (fun b => ?_) h
      · rw [Pi.add_apply, facetPoint_mid]
        have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
            (Fin.castAdd j (Fin.last i)) = 0 := by
          rw [unit_apply_ne]
          intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
          have hlt := a.isLt
          omega
        rw [hzero, add_zero]
        exact ⟨by norm_num, by omega⟩
      · rw [Pi.add_apply, facetPoint_head]
        by_cases hba : b = a
        · subst hba
          rw [unit_apply_self]
          refine ⟨by have := hy2 b; omega, ?_⟩
          have h := (hys.1 (Fin.castAdd j (Fin.castSucc b))).2
          rw [facetPoint_head] at h
          omega
        · have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
              (Fin.castAdd j (Fin.castSucc b)) = 0 := by
            rw [unit_apply_ne]
            intro hh
            exact hba (Fin.ext (by
              have hv := congrArg Fin.val hh
              simp only [Fin.val_castAdd, Fin.val_castSucc] at hv
              omega))
          rw [hzero, add_zero]
          have h := hys.1 (Fin.castAdd j (Fin.castSucc b))
          rw [facetPoint_head] at h
          exact h
    · intro b
      rw [Pi.add_apply, facetPoint_tail]
      have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
          (Fin.natAdd (i + 1) b) = 0 := by
        rw [unit_apply_ne]
        intro hh
        have hv := congrArg Fin.val hh
        simp [Fin.castAdd, Fin.natAdd] at hv
        omega
      rw [hzero, add_zero]
      exact ⟨by norm_num, by omega⟩
  obtain ⟨i', j', hij, z, hz2, hzs, hi', hodo⟩ :=
    facet_normal_form (i + 1 + j) M _ hpos (Fin.castAdd j (Fin.last i)) hmid
  -- the time comparison at the sorted point
  have h := odo_facet_two_ge_prev (i := i') (j := j') (M := M) (t := t) ht
    (hi' ⟨Fin.castAdd j (Fin.castSucc a), by
      rw [Pi.add_apply, facetPoint_head, unit_apply_self]
      have := hy2 a
      omega⟩) hM (hS i' j' hij (hi' ⟨Fin.castAdd j (Fin.castSucc a), by
      rw [Pi.add_apply, facetPoint_head, unit_apply_self]
      have := hy2 a
      omega⟩)) z ⟨⟨0, by
        have h := hi' ⟨Fin.castAdd j (Fin.castSucc a), by
          rw [Pi.add_apply, facetPoint_head, unit_apply_self]
          have := hy2 a
          omega⟩
        omega⟩, hz2 ⟨0, by
        have h := hi' ⟨Fin.castAdd j (Fin.castSucc a), by
          rw [Pi.add_apply, facetPoint_head, unit_apply_self]
          have := hy2 a
          omega⟩
        omega⟩⟩ hzs
  -- transport back: `hodo` identifies the raw and sorted odometers at every time
  rw [← (hodo (t - 1)).1] at h
  rw [← (hodo t).2] at h
  -- the right side is `facetPoint y 2 j + unit (head a)`
  have hpt : facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a))
      + unit (Fin.castAdd j (Fin.last i))
      = facetPoint y 2 j + unit (Fin.castAdd j (Fin.castSucc a)) := by
    have h1 : facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i)) = facetPoint y 2 j := by
      rw [facetPoint_add_mid_point y 1]
      norm_num
    calc facetPoint y 1 j + unit (Fin.castAdd j (Fin.castSucc a))
          + unit (Fin.castAdd j (Fin.last i))
        = facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i))
          + unit (Fin.castAdd j (Fin.castSucc a)) := by abel
      _ = facetPoint y 2 j + unit (Fin.castAdd j (Fin.castSucc a)) := by rw [h1]
  rw [hpt] at h
  exact h

end DimRed
