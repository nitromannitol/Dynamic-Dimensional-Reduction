/-
Weak facet compatibility in every dimension, the clause
`base_dimension:weak_compatability` of `dimred.tex:919-926`.

The zero-head case is the unconditional facet Laplacian calculation.  For a
positive head dimension, the remaining head contribution is exposed as the
inductive bound used in the paper's Section 5 argument (`dimred.tex:1155-1160`).
-/
import DimRed.Support.FacetLap
import DimRed.Support.FacetNbr

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

theorem weak_facet_general (M i j : ℕ) (_hM : 2 ≤ M)
    (t : ℕ) (_ht : 1 ≤ t) (x : Fin i → ℤ) (_hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hhead : 1 ≤ i →
      (∑ a : Fin i,
        (odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 1 j) +
          odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 1 j) -
          2 * odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j))) ≤ (j : ℤ))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) =
        odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  by_cases hi : i = 0
  · subst i
    have htail_sub : ∀ l : Fin (0 + 1 + j), IsTail l →
        odo (0 + 1 + j) (2 * M)
            (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
            (facetPoint x 1 j - unit l) =
          odo (0 + 1 + j) (2 * M)
            (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) := by
      intro l
      refine Fin.addCases ?_ (fun b _ => ?_) l
      · intro a ha
        have ha0 : a = Fin.last 0 := Fin.eq_zero a
        subst ha0
        have : ¬ IsTail (Fin.castAdd j (Fin.last 0)) := by
          simp [IsTail]
        exact False.elim (this ha)
      · exact odo_facetPoint_sub_tail (M := M) x
          (2 * ((0 + 1 + j : ℕ) : ℤ)) t b
    have htail_add : ∀ l : Fin (0 + 1 + j), IsTail l →
        odo (0 + 1 + j) (2 * M)
            (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
            (facetPoint x 1 j + unit l) =
          odo (0 + 1 + j) (2 * M)
            (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) := by
      intro l
      refine Fin.addCases ?_ (fun b _ => ?_) l
      · intro a ha
        have ha0 : a = Fin.last 0 := Fin.eq_zero a
        subst ha0
        have : ¬ IsTail (Fin.castAdd j (Fin.last 0)) := by
          simp [IsTail]
        exact False.elim (this ha)
      · exact odo_facetPoint_add_tail (M := M) x
          (2 * ((0 + 1 + j : ℕ) : ℤ)) t b
    have hmid_sub : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j - unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) :=
      odo_facetPoint_sub_mid (M := M) (j := j) x
        (2 * ((0 + 1 + j : ℕ) : ℤ)) t
    have hmid_add : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j + unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) :=
      odo_facetPoint_add_mid (M := M) (j := j) x
        (2 * ((0 + 1 + j : ℕ) : ℤ)) t
    have hv : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) =
        odo (0 + 1 + j) (2 * M)
          (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) + 1 := by
      simpa [odoUnif] using h
    exact odo_succ_facetPoint_zero x t htail_sub htail_add hmid_sub hmid_add hv (by omega)
  · have hi_pos : 1 ≤ i := by omega
    have htail_sub : ∀ l : Fin (i + 1 + j), IsTail l →
        odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t
            (facetPoint x 1 j - unit l) =
          odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) := by
      intro l
      refine Fin.addCases ?_ (fun b _ => ?_) l
      · intro a ha
        have ha_val : i + 1 ≤ (a : ℕ) := by simpa [IsTail] using ha
        have ha_lt : (a : ℕ) < i + 1 := a.isLt
        have ha_last : a = Fin.last i := by
          apply Fin.ext
          omega
        subst ha_last
        exact odo_facetPoint_sub_mid (M := M) (j := j) x
          (2 * ((i + 1 + j : ℕ) : ℤ)) t
      · exact odo_facetPoint_sub_tail (M := M) x
          (2 * ((i + 1 + j : ℕ) : ℤ)) t b
    have htail_add : ∀ l : Fin (i + 1 + j), IsTail l →
        odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t
            (facetPoint x 1 j + unit l) =
          odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) := by
      intro l
      refine Fin.addCases ?_ (fun b _ => ?_) l
      · intro a ha
        have ha_val : i + 1 ≤ (a : ℕ) := by simpa [IsTail] using ha
        have ha_lt : (a : ℕ) < i + 1 := a.isLt
        have ha_last : a = Fin.last i := by
          apply Fin.ext
          omega
        subst ha_last
        exact odo_facetPoint_add_mid (M := M) (j := j) x
          (2 * ((i + 1 + j : ℕ) : ℤ)) t
      · exact odo_facetPoint_add_tail (M := M) x
          (2 * ((i + 1 + j : ℕ) : ℤ)) t b
    have hmid_sub : odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j - unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) :=
      odo_facetPoint_sub_mid (M := M) (j := j) x
        (2 * ((i + 1 + j : ℕ) : ℤ)) t
    have hmid_add : odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j + unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) :=
      odo_facetPoint_add_mid (M := M) (j := j) x
        (2 * ((i + 1 + j : ℕ) : ℤ)) t
    have hhead' : ∀ a : Fin i,
        facetPoint x 1 j + unit (facetHead a) = facetPoint (x + unit a) 1 j ∧
        facetPoint x 1 j - unit (facetHead a) = facetPoint (x - unit a) 1 j := by
      intro a
      exact ⟨facetPoint_add_head x a, facetPoint_sub_head x a⟩
    have hlap := lap_facetPoint (i := i) (j := j) (M := M)
      (2 * ((i + 1 + j : ℕ) : ℤ)) x t htail_sub htail_add hmid_sub hmid_add hhead'
    have hv : odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) =
        odo (i + 1 + j) (2 * M)
          (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) + 1 := by
      simpa [odoUnif] using h
    have hhead_raw :
        (∑ a : Fin i,
          (odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x + unit a) 1 j) +
            odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x - unit a) 1 j) -
            2 * odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j))) ≤ (j : ℤ) := by
      simpa [odoUnif] using hhead hi_pos
    have hsum_rewrite :
        (∑ a : Fin i,
          (odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x + unit a) 1 j) +
            odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x - unit a) 1 j))) -
          2 * (i : ℤ) * odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) =
        ∑ a : Fin i,
          (odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x + unit a) 1 j) +
            odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint (x - unit a) 1 j) -
            2 * odo (i + 1 + j) (2 * M)
              (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j)) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, Finset.card_univ]
      ring
    have hgap : odo (i + 1 + j) (2 * M)
          (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j) -
        odo (i + 1 + j) (2 * M)
          (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) = -1 := by
      linarith [hv]
    have hjz : (0 : ℤ) ≤ (j : ℤ) := by omega
    have hlap_le : lap (odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t) (facetPoint x 1 j) ≤ -1 := by
      rw [hlap, hsum_rewrite, hgap]
      nlinarith [hhead_raw]
    have hcube : inCube (i + 1 + j) (2 * M) (facetPoint x 1 j) :=
      inSimplex_inCube (i + 1 + j) M (facetPoint x 1 j) hxs
    have hstep := odo_succ_eq (i + 1 + j) (2 * M)
      (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) hcube
    have hnot : ¬ 2 * ((i + 1 + j : ℕ) : ℤ) ≤
        2 * ((i + 1 + j : ℕ) : ℤ) +
          lap (odo (i + 1 + j) (2 * M)
            (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t) (facetPoint x 1 j) := by
      linarith [hlap_le]
    change odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) (t + 1) (facetPoint x 1 j) =
      odo (i + 1 + j) (2 * M)
        (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j)
    simp only [sandp] at hstep
    rw [if_neg hnot, add_zero] at hstep
    exact hstep

end DimRed
