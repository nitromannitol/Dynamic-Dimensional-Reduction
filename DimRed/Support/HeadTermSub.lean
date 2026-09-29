import DimRed.Support.StrongRawLe
import DimRed.Support.RegFacetTime
import DimRed.Support.RegFacetStep

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

theorem nbrSum_facetPoint_one {j M t : ℕ} :
    nbrSum (odoUnif (1 + 1 + j) (2 * M) t) (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j)
      = ((1 + 1 + j : ℕ) : ℤ) *
        (odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)
          + odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j)) := by
  rw [nbrSum]
  -- split the sum into the head direction and the tail directions
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_one]
  -- the head direction
  have hhead : odoUnif (1 + 1 + j) (2 * M) t
        (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j + unit (Fin.castAdd j (Fin.castSucc 0)))
      + odoUnif (1 + 1 + j) (2 * M) t
        (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j - unit (Fin.castAdd j (Fin.castSucc 0)))
      = odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)
        + odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) := by
    congr 1
    · rw [facetPoint_add_head']
      congr 1
      funext l
      refine Fin.addCases ?_ ?_ l
      · intro h
        refine Fin.lastCases ?_ (fun b => ?_) h
        · rw [facetPoint_mid, facetPoint_mid]
        · rw [facetPoint_head, facetPoint_head]
          have hb : (b : ℕ) < 1 := b.isLt
          have hba : b = (0 : Fin 1) := Fin.ext (by omega)
          rw [hba]
          simp [unit]
      · intro b
        rw [facetPoint_tail, facetPoint_tail]
    · -- the `-e_0` neighbour is the point itself by reflection
      have hpt : facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j - unit (Fin.castAdd j (Fin.castSucc 0))
          = fun k => if k = (Fin.castAdd j (Fin.castSucc 0) : Fin (1 + 1 + j))
              then 1 - (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) (Fin.castAdd j (Fin.castSucc 0))
              else (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) k := by
        funext k
        by_cases hk : k = (Fin.castAdd j (Fin.castSucc 0) : Fin (1 + 1 + j))
        · rw [hk, Pi.sub_apply, unit_apply_self, facetPoint_head]
          norm_num
        · rw [Pi.sub_apply, unit_apply_ne hk, sub_zero, if_neg hk]
      rw [hpt]
      simp only [odoUnif]
      rw [odo_reflect_coord]
  rw [hhead]
  -- the tail directions: each gives the head-raised point plus the point itself
  have htail : ∀ b : Fin j,
      odoUnif (1 + 1 + j) (2 * M) t
        (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j + unit (Fin.natAdd (1 + 1) b))
      + odoUnif (1 + 1 + j) (2 * M) t
        (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j - unit (Fin.natAdd (1 + 1) b))
      = odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)
        + odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) := by
    intro b
    have h1 := odo_facetPoint_add_tail (i := 1) (j := j) (M := M)
      (fun _ : Fin 1 => (1 : ℤ)) (2 * ((1 + 1 + j : ℕ) : ℤ)) t b
    have h2 := odo_facetPoint_sub_tail (i := 1) (j := j) (M := M)
      (fun _ : Fin 1 => (1 : ℤ)) (2 * ((1 + 1 + j : ℕ) : ℤ)) t b
    simp only [odoUnif] at h1 h2 ⊢
    rw [h1, h2]
    have hswap := facetPoint_one_two_refl (j := j) (M := M) (t := t)
    simp only [odoUnif] at hswap
    rw [← hswap]
  rw [Finset.sum_congr rfl (fun b _ => htail b)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmid' : facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j + unit (Fin.castAdd j (Fin.last 1))
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) 2 j := by
    rw [facetPoint_add_mid_point]
    norm_num
  rw [hmid']
  -- the `-e_mid` neighbour reflects to the point itself
  have hrefl : odoUnif (1 + 1 + j) (2 * M) t
      (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j - unit (Fin.castAdd j (Fin.last 1)))
      = odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) := by
    have hpt : facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j - unit (Fin.castAdd j (Fin.last 1))
        = fun k => if k = (Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j))
            then 1 - (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) (Fin.castAdd j (Fin.last 1))
            else (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j) k := by
      funext k
      by_cases hk : k = (Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j))
      · rw [hk, Pi.sub_apply, unit_apply_self, facetPoint_mid]
        norm_num
      · rw [Pi.sub_apply, unit_apply_ne hk, sub_zero, if_neg hk]
    rw [hpt]
    simp only [odoUnif]
    rw [odo_reflect_coord]
  rw [hrefl]
  have hswap := facetPoint_one_two_refl (j := j) (M := M) (t := t)
  simp only [odoUnif] at hswap ⊢
  rw [← hswap]
  push_cast
  ring
theorem head_field_one (j M t : ℕ) (ht : 1 ≤ t) (hM : 2 ≤ M)
    (hS : RegStrongFacet (1 + 1 + j) M (t - 1))
    (hys : inSimplex (1 + 1 + j) M (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j))
    (_hgap : odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j)
      = odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j) + 1) :
    odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => (3 : ℤ)) 1 j)
      + odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j)
      ≤ odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (3 : ℤ)) 2 j)
      + odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 2 j) := by
  have hadd := head_term_add (i := 1) (j := j) (M := M) (t := t) ht (by omega) hM
    (fun i' j' hij hi' => by
      have h : i' + 1 + j' = 1 + 1 + j := hij
      rw [h]
      exact hS) (fun _ : Fin 1 => (2 : ℤ)) (fun _ => by norm_num) hys ⟨0, by omega⟩
  have hsub := head_term_sub_one (j := j) (M := M) (t := t) ht hM hS hys
  have h1 : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) + unit (0 : Fin 1)) 1 j
      = facetPoint (fun _ : Fin 1 => (3 : ℤ)) 1 j := facetPoint_two_add_head (j := j) (c := 1)
  have h2 : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) + unit (0 : Fin 1)) 2 j
      = facetPoint (fun _ : Fin 1 => (3 : ℤ)) 2 j := facetPoint_two_add_head (j := j) (c := 2)
  have h3 : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) - unit (0 : Fin 1)) 1 j
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j := facetPoint_two_sub_head (j := j) (c := 1)
  have h4 : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) - unit (0 : Fin 1)) 2 j
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) 2 j := facetPoint_two_sub_head (j := j) (c := 2)
  have h1' : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) + unit (⟨0, by omega⟩ : Fin 1)) 1 j
      = facetPoint (fun _ : Fin 1 => (3 : ℤ)) 1 j := h1
  have h2' : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) + unit (⟨0, by omega⟩ : Fin 1)) 2 j
      = facetPoint (fun _ : Fin 1 => (3 : ℤ)) 2 j := h2
  have h3' : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) - unit (⟨0, by omega⟩ : Fin 1)) 1 j
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j := h3
  have h4' : facetPoint ((fun _ : Fin 1 => (2 : ℤ)) - unit (⟨0, by omega⟩ : Fin 1)) 2 j
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) 2 j := h4
  rw [h1', h2'] at hadd
  -- `hsub` is already in the `facetPoint (fun _ => 2)` form
  linarith
end DimRed
