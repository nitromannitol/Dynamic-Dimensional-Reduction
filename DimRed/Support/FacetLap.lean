module

public import DimRed.Support.Recursion

@[expose] public section

/-
The Laplacian at a facet point, the subsection labelled `subsec:dim_reduction` in `dimred-corrected-arxiv.tex` and the weak facet
compatibility clause `base_dimension:weak_compatability` of `dimred-corrected-arxiv.tex`, after the neighbour terms are supplied by
symmetry.
-/

namespace DimRed

open LatticeProb

def IsTail {i j : ℕ} (l : Fin (i + 1 + j)) : Prop := i + 1 ≤ (l : ℕ)

def facetHead {i j : ℕ} (a : Fin i) : Fin (i + 1 + j) :=
  Fin.castAdd j a.castSucc

def facetMid {i j : ℕ} : Fin (i + 1 + j) := Fin.castAdd j (Fin.last i)

theorem lap_facetPoint {i j M : ℕ} (c' : ℤ) (x : Fin i → ℤ) (t : ℕ)
    (htail_sub : ∀ l : Fin (i + 1 + j), IsTail l →
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit l) = odo (i + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 1 j))
    (htail_add : ∀ l : Fin (i + 1 + j), IsTail l →
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit l) = odo (i + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 2 j))
    (hmid_sub : odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j))
    (hmid_add : odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j))
    (hhead : ∀ a : Fin i,
      facetPoint x 1 j + unit (facetHead a) = facetPoint (x + unit a) 1 j ∧
      facetPoint x 1 j - unit (facetHead a) = facetPoint (x - unit a) 1 j) :
    lap (odo (i + 1 + j) (2 * M) (fun _ => c') t) (facetPoint x 1 j) =
      (∑ a : Fin i,
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x + unit a) 1 j) +
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x - unit a) 1 j))) -
        2 * (i : ℤ) * odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j) +
      ((j : ℤ) + 1) *
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) -
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)) := by
  let v : Site (i + 1 + j) → ℤ := odo (i + 1 + j) (2 * M) (fun _ => c') t
  let p : Site (i + 1 + j) := facetPoint x 1 j
  let q : Site (i + 1 + j) := facetPoint x 2 j
  have htail : ∀ l : Fin j,
      v (p + unit (Fin.natAdd (i + 1) l)) + v (p - unit (Fin.natAdd (i + 1) l)) = v q + v p := by
    intro l
    have hl : IsTail (Fin.natAdd (i + 1) l) := by
      simp [IsTail]
    change odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (Fin.natAdd (i + 1) l)) +
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (Fin.natAdd (i + 1) l)) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) +
        odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)
    rw [htail_add (Fin.natAdd (i + 1) l) hl,
      htail_sub (Fin.natAdd (i + 1) l) hl]
  have hmid :
      v (p + unit (facetMid (i := i) (j := j))) +
          v (p - unit (facetMid (i := i) (j := j))) = v q + v p := by
    change odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (facetMid (i := i) (j := j))) +
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) +
        odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)
    rw [hmid_add, hmid_sub]
  have hhead' : ∀ a : Fin i,
      v (p + unit (facetHead a)) + v (p - unit (facetHead a)) =
        v (facetPoint (x + unit a) 1 j) + v (facetPoint (x - unit a) 1 j) := by
    intro a
    rw [(hhead a).1, (hhead a).2]
  have hsum : nbrSum v p =
      (∑ a : Fin i, (v (facetPoint (x + unit a) 1 j) +
        v (facetPoint (x - unit a) 1 j))) + ((j : ℤ) + 1) * (v q + v p) := by
    have hheadsum :
        (∑ a : Fin i, (v (p + unit (facetHead a)) +
          v (p - unit (facetHead a)))) =
          ∑ a : Fin i, (v (facetPoint (x + unit a) 1 j) +
            v (facetPoint (x - unit a) 1 j)) :=
      Finset.sum_congr rfl (fun a _ => hhead' a)
    have hheadsum' :
        (∑ a : Fin i, (v (p + unit (Fin.castAdd j a.castSucc)) +
          v (p - unit (Fin.castAdd j a.castSucc)))) =
          ∑ a : Fin i, (v (facetPoint (x + unit a) 1 j) +
            v (facetPoint (x - unit a) 1 j)) := by
      simpa [facetHead] using hheadsum
    have hmidsum :
        v (p + unit (Fin.castAdd j (Fin.last i))) +
            v (p - unit (Fin.castAdd j (Fin.last i))) = v q + v p := by
      simpa [facetMid] using hmid
    have htailsum :
        (∑ l : Fin j, (v (p + unit (Fin.natAdd (i + 1) l)) +
          v (p - unit (Fin.natAdd (i + 1) l)))) =
          ∑ l : Fin j, (v q + v p) :=
      Finset.sum_congr rfl (fun l _ => htail l)
    simp only [nbrSum]
    rw [Fin.sum_univ_add]
    rw [Fin.sum_univ_castSucc]
    rw [hheadsum', hmidsum, htailsum]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  dsimp [lap, v, p, q] at hsum ⊢
  rw [hsum]
  norm_num at *
  ring

/-- The Laplacian at the mid facet point `(x, 2, 1_j)`, the same decomposition as
`lap_facetPoint` with the head replaced by the mid. -/
theorem lap_facetPoint_two {i j M : ℕ} (c' : ℤ) (x : Fin i → ℤ) (t : ℕ)
    (htail_sub : ∀ l : Fin (i + 1 + j), IsTail l →
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j - unit l) = odo (i + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 3 j))
    (htail_add : ∀ l : Fin (i + 1 + j), IsTail l →
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j + unit l) = odo (i + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 3 j))
    (hmid_sub : odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j - unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j))
    (hmid_add : odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j + unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j))
    (hhead : ∀ a : Fin i,
      facetPoint x 3 j + unit (facetHead a) = facetPoint (x + unit a) 2 j ∧
      facetPoint x 3 j - unit (facetHead a) = facetPoint (x - unit a) 2 j) :
    lap (odo (i + 1 + j) (2 * M) (fun _ => c') t) (facetPoint x 3 j) =
      (∑ a : Fin i,
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x + unit a) 2 j) +
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint (x - unit a) 2 j))) -
        2 * (i : ℤ) * odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j) +
      ((j : ℤ) + 1) *
        (odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j) -
          odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j)) := by
  let v : Site (i + 1 + j) → ℤ := odo (i + 1 + j) (2 * M) (fun _ => c') t
  let p : Site (i + 1 + j) := facetPoint x 3 j
  let q : Site (i + 1 + j) := facetPoint x 3 j
  have htail : ∀ l : Fin j,
      v (p + unit (Fin.natAdd (i + 1) l)) + v (p - unit (Fin.natAdd (i + 1) l)) = v q + v p := by
    intro l
    have hl : IsTail (Fin.natAdd (i + 1) l) := by
      simp [IsTail]
    change odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j + unit (Fin.natAdd (i + 1) l)) +
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j - unit (Fin.natAdd (i + 1) l)) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j) +
        odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j)
    rw [htail_add (Fin.natAdd (i + 1) l) hl,
      htail_sub (Fin.natAdd (i + 1) l) hl]
  have hmid :
      v (p + unit (facetMid (i := i) (j := j))) +
          v (p - unit (facetMid (i := i) (j := j))) = v q + v p := by
    change odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j + unit (facetMid (i := i) (j := j))) +
      odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 3 j - unit (facetMid (i := i) (j := j))) =
      odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j) +
        odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 3 j)
    rw [hmid_add, hmid_sub]
  have hhead' : ∀ a : Fin i,
      v (p + unit (facetHead a)) + v (p - unit (facetHead a)) =
        v (facetPoint (x + unit a) 2 j) + v (facetPoint (x - unit a) 2 j) := by
    intro a
    rw [(hhead a).1, (hhead a).2]
  have hsum : nbrSum v p =
      (∑ a : Fin i, (v (facetPoint (x + unit a) 2 j) +
        v (facetPoint (x - unit a) 2 j))) + ((j : ℤ) + 1) * (v q + v p) := by
    have hheadsum :
        (∑ a : Fin i, (v (p + unit (facetHead a)) +
          v (p - unit (facetHead a)))) =
          ∑ a : Fin i, (v (facetPoint (x + unit a) 2 j) +
            v (facetPoint (x - unit a) 2 j)) :=
      Finset.sum_congr rfl (fun a _ => hhead' a)
    have hheadsum' :
        (∑ a : Fin i, (v (p + unit (Fin.castAdd j a.castSucc)) +
          v (p - unit (Fin.castAdd j a.castSucc)))) =
          ∑ a : Fin i, (v (facetPoint (x + unit a) 2 j) +
            v (facetPoint (x - unit a) 2 j)) := by
      simpa [facetHead] using hheadsum
    have hmidsum :
        v (p + unit (Fin.castAdd j (Fin.last i))) +
            v (p - unit (Fin.castAdd j (Fin.last i))) = v q + v p := by
      simpa [facetMid] using hmid
    have htailsum :
        (∑ l : Fin j, (v (p + unit (Fin.natAdd (i + 1) l)) +
          v (p - unit (Fin.natAdd (i + 1) l)))) =
          ∑ l : Fin j, (v q + v p) :=
      Finset.sum_congr rfl (fun l _ => htail l)
    simp only [nbrSum]
    rw [Fin.sum_univ_add]
    rw [Fin.sum_univ_castSucc]
    rw [hheadsum', hmidsum, htailsum]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  dsimp [lap, v, p, q] at hsum ⊢
  rw [hsum]
  norm_num at *
  ring

theorem lap_facetPoint_zero {j M : ℕ} (c' : ℤ) (x : Fin 0 → ℤ) (t : ℕ)
    (htail_sub : ∀ l : Fin (0 + 1 + j), IsTail l →
      odo (0 + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit l) = odo (0 + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 1 j))
    (htail_add : ∀ l : Fin (0 + 1 + j), IsTail l →
      odo (0 + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit l) = odo (0 + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 2 j))
    (hmid_sub : odo (0 + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j))
    (hmid_add : odo (0 + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j))
    :
    lap (odo (0 + 1 + j) (2 * M) (fun _ => c') t) (facetPoint x 1 j) =
      ((j : ℤ) + 1) *
        (odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) -
          odo (0 + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j)) := by
  have hhead : ∀ a : Fin 0,
      facetPoint x 1 j + unit (facetHead a) = facetPoint (x + unit a) 1 j ∧
      facetPoint x 1 j - unit (facetHead a) = facetPoint (x - unit a) 1 j := by
    intro a
    exact Fin.elim0 a
  have h := lap_facetPoint (i := 0) (j := j) (M := M) c' x t
    htail_sub htail_add hmid_sub hmid_add hhead
  simpa using h

theorem odo_succ_facetPoint_zero {j M : ℕ} (x : Fin 0 → ℤ) (t : ℕ)
    (htail_sub : ∀ l : Fin (0 + 1 + j), IsTail l →
      odo (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j - unit l) = odo (0 + 1 + j) (2 * M)
          (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j))
    (htail_add : ∀ l : Fin (0 + 1 + j), IsTail l →
      odo (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j + unit l) = odo (0 + 1 + j) (2 * M)
          (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 2 j))
    (hmid_sub : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j - unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j))
    (hmid_add : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 1 j + unit (facetMid (i := 0) (j := j))) =
      odo (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 2 j))
    (hv : odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) =
      odo (0 + 1 + j) (2 * M) (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t
        (facetPoint x 2 j) + 1)
    (hj : 1 ≤ j + 1) :
    odoUnif (0 + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) =
      odoUnif (0 + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  have hlap := lap_facetPoint_zero (j := j) (M := M)
    (2 * ((0 + 1 + j : ℕ) : ℤ)) x t htail_sub htail_add hmid_sub hmid_add
  have hlap' : lap (odo (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t) (facetPoint x 1 j) =
      -((j : ℤ) + 1) := by
    rw [hlap, hv]
    ring
  by_cases hx : inCube (0 + 1 + j) (2 * M) (facetPoint x 1 j)
  · change odo (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t + 1) (facetPoint x 1 j) =
      odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j)
    have hs := odo_succ_eq (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j) hx
    simp only [sandp] at hs
    have hnot : ¬ 2 * ((0 + 1 + j : ℕ) : ℤ) ≤
        2 * ((0 + 1 + j : ℕ) : ℤ) +
          lap (odo (0 + 1 + j) (2 * M)
            (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t) (facetPoint x 1 j) := by
      rw [hlap']
      omega
    rw [hs, if_neg hnot, add_zero]
  · change odo (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t + 1) (facetPoint x 1 j) =
      odo (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t (facetPoint x 1 j)
    rw [odo_eq_zero_outside (0 + 1 + j) (2 * M)
      (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) (t + 1) _ hx,
      odo_eq_zero_outside (0 + 1 + j) (2 * M)
        (fun _ => 2 * ((0 + 1 + j : ℕ) : ℤ)) t _ hx]

end DimRed
