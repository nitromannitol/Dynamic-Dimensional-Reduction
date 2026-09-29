import DimRed.Support.StrongRawLe
import DimRed.Support.RegFacetTime

/-!
# The head term of the facet comparison at `y - unit a`

The companion of `head_term_add`: the head neighbour in the negative direction,
`facetPoint (y - unit a) 1 j`, is dominated at time `t - 1` by its mid
counterpart at time `t`, whenever the shifted point still has a coordinate at
least two.  This is the paper's `v_t(y_i, 2, 1_j) >= v_{t-1}(y_i, 1, 1_j)` for
`y_i >= 2` (`dimred.tex:1345-1348`), and it is `strong_raw_le` at the shifted
point in the mid direction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The head term of the facet comparison at `y - unit a`, from the one-step
domination at the facet normal form of the head neighbour. -/
theorem head_term_sub (i j M t : ℕ) (ht : 1 ≤ t) (hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : RegStrongFacet (i + 1 + j) M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∀ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) (a : Fin i)
    (h2 : ∃ l, 2 ≤ (facetPoint (y - unit a) 1 j) l) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint (y - unit a) 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint (y - unit a) 2 j) := by
  have hshift : facetPoint (y - unit a) 1 j
      = facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a)) := by
    rw [facetPoint_sub_head']
  have hshift2 : facetPoint (y - unit a) 2 j
      = facetPoint y 2 j - unit (Fin.castAdd j (Fin.castSucc a)) := by
    rw [facetPoint_sub_head']
  rw [hshift] at h2
  rw [hshift, hshift2]
  -- the shifted point has mid coordinate one, so the mid direction is the
  -- direction of the clause
  have hmid : (facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a)))
      (Fin.castAdd j (Fin.last i)) = 1 := by
    rw [Pi.sub_apply, facetPoint_mid]
    have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
        (Fin.castAdd j (Fin.last i)) = 0 := by
      rw [unit_apply_ne]
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
      have hlt := a.isLt
      omega
    rw [hzero, sub_zero]
  have hpos : inPos (i + 1 + j) M
      (facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a))) := by
    intro l
    refine Fin.addCases ?_ ?_ l
    · intro h
      refine Fin.lastCases ?_ (fun b => ?_) h
      · rw [Pi.sub_apply, facetPoint_mid]
        have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
            (Fin.castAdd j (Fin.last i)) = 0 := by
          rw [unit_apply_ne]
          intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
          have hlt := a.isLt
          omega
        rw [hzero, sub_zero]
        exact ⟨by norm_num, by omega⟩
      · rw [Pi.sub_apply, facetPoint_head]
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
          rw [hzero, sub_zero]
          have h := hys.1 (Fin.castAdd j (Fin.castSucc b))
          rw [facetPoint_head] at h
          exact h
    · intro b
      rw [Pi.sub_apply, facetPoint_tail]
      have hzero : (unit (Fin.castAdd j (Fin.castSucc a)) : Site (i + 1 + j))
          (Fin.natAdd (i + 1) b) = 0 := by
        rw [unit_apply_ne]
        intro hh
        have hv := congrArg Fin.val hh
        simp [Fin.castAdd, Fin.natAdd] at hv
        omega
      rw [hzero, sub_zero]
      exact ⟨by norm_num, by omega⟩
  -- the one-step domination at the shifted point in the mid direction
  have h := strong_raw_le (i + 1 + j) M (t - 1) (by omega) (by omega) (hS)
    (facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a))) hpos
    (Fin.castAdd j (Fin.last i)) hmid h2
  have hmid' : facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a))
      + unit (Fin.castAdd j (Fin.last i))
      = facetPoint y 2 j - unit (Fin.castAdd j (Fin.castSucc a)) := by
    have h1 : facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i)) = facetPoint y 2 j := by
      rw [facetPoint_add_mid_point y 1]
      norm_num
    calc facetPoint y 1 j - unit (Fin.castAdd j (Fin.castSucc a))
          + unit (Fin.castAdd j (Fin.last i))
        = facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i))
          - unit (Fin.castAdd j (Fin.castSucc a)) := by abel
      _ = facetPoint y 2 j - unit (Fin.castAdd j (Fin.castSucc a)) := by rw [h1]
  rw [hmid'] at h
  have ht1 : t - 1 + 1 = t := by omega
  rw [ht1] at h
  exact h


/-- The all-ones sub-case of the head field: when `i = 1` and the head
coordinate is `2`, the shifted `1 j` point is `(1, 1_j)` and the shifted `2 j`
point is `(1, 2, 1_j)`, which is the `i = 1` instance of the time comparison. -/
theorem head_term_sub_one (j M t : ℕ) (ht : 1 ≤ t) (hM : 2 ≤ M)
    (hS : RegStrongFacet (1 + 1 + j) M (t - 1))
    (hys : inSimplex (1 + 1 + j) M (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)) :
    odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)
      ≤ odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 2 j) :=
  odo_facet_two_ge_prev_one (j := j) (M := M) (t := t) ht hM hS 2 le_rfl hys

end DimRed
