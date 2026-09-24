import DimRed.Support.AxisStep
import DimRed.Support.Difference

/-
The coordinate evaluations and neighbour identities at a facet point
`(x_i, 1, 1_j)` from `dimred.tex:918-943`.
-/
namespace DimRed

open LatticeProb

theorem facetPoint_head {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) (a : Fin i) :
    facetPoint x c j (Fin.castAdd j (Fin.castSucc a)) = x a := by
  simp [facetPoint]

theorem facetPoint_mid {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) :
    facetPoint x c j (Fin.castAdd j (Fin.last i)) = c := by
  simp [facetPoint]

theorem facetPoint_tail {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) (b : Fin j) :
    facetPoint x c j (Fin.natAdd (i + 1) b) = 1 := by
  simp [facetPoint]

theorem facetPoint_add_head {i j : ℕ} (x : Fin i → ℤ) (a : Fin i) :
    facetPoint x 1 j + unit (Fin.castAdd j (Fin.castSucc a))
      = facetPoint (x + unit a) 1 j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · simp [facetPoint]
      apply unit_apply_ne
      intro h
      exact Fin.castSucc_ne_last a (Fin.castAdd_injective _ _ h.symm)
    · by_cases hab : b = a
      · subst hab; simp [facetPoint, unit_apply_self]
      · simp [facetPoint]
        rw [unit_apply_ne]
        · exact (unit_apply_ne hab).symm
        · intro h
          exact hab (Fin.castSucc_injective _ (Fin.castAdd_injective _ _ h))
  · intro b
    simp [facetPoint]
    apply unit_apply_ne
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
    omega

theorem facetPoint_sub_head {i j : ℕ} (x : Fin i → ℤ) (a : Fin i) :
    facetPoint x 1 j - unit (Fin.castAdd j (Fin.castSucc a))
      = facetPoint (x - unit a) 1 j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · simp [facetPoint]
      apply unit_apply_ne
      intro h
      exact Fin.castSucc_ne_last a (Fin.castAdd_injective _ _ h.symm)
    · by_cases hab : b = a
      · subst hab; simp [facetPoint, unit_apply_self]
      · simp [facetPoint]
        rw [unit_apply_ne]
        · exact (unit_apply_ne hab).symm
        · intro h
          exact hab (Fin.castSucc_injective _ (Fin.castAdd_injective _ _ h))
  · intro b
    simp [facetPoint]
    apply unit_apply_ne
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
    omega

theorem facetPoint_add_mid_point {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) :
    facetPoint x c j + unit (Fin.castAdd j (Fin.last i))
      = facetPoint x (c + 1) j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro h
    refine Fin.lastCases ?_ (fun a => ?_) h
    · rw [Pi.add_apply, unit_apply_self]
      simp [facetPoint]
    · rw [Pi.add_apply, unit_apply_ne]
      · simp [facetPoint]
      · intro h'
        have hv := congrArg Fin.val h'
        simp [Fin.castAdd, Fin.castLE] at hv
        omega
  · intro b
    rw [Pi.add_apply, unit_apply_ne]
    · simp [facetPoint]
    · intro h'
      have hv := congrArg Fin.val h'
      simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
      omega

theorem reflect_sub_of_one {d : ℕ} (u : Site d) (q : Fin d) (hu : u q = 1) :
    (fun k => if k = q then 1 - (u - unit q) q else (u - unit q) k) = u := by
  funext k
  by_cases hk : k = q
  · subst hk
    rw [if_pos rfl, sub_unit_self, hu]
    norm_num
  · rw [if_neg hk, sub_unit_other _ _ _ _ hk]

theorem swap_add_eq_add {d : ℕ} (u : Site d) (i j : Fin d) (hij : i ≠ j)
    (he : u i = u j) :
    (fun l => (u + unit j) (Equiv.swap i j l)) = u + unit i := by
  funext l
  by_cases hli : l = i
  · subst l
    rw [Equiv.swap_apply_left, add_unit_self, add_unit_self, he]
  · by_cases hlj : l = j
    · subst l
      rw [Equiv.swap_apply_right, add_unit_other d u j i hij,
        add_unit_other d u i j hij.symm]
      exact he
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj,
        add_unit_other d u j l hlj, add_unit_other d u i l hli]

theorem odo_facetPoint_sub_tail {i j M : ℕ} (x : Fin i → ℤ) (c' : ℤ) (t : ℕ)
    (l : Fin j) :
    odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (Fin.natAdd (i + 1) l))
      = odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j) := by
  have h := odo_reflect_coord (i + 1 + j) M c' t
    (facetPoint x 1 j - unit (Fin.natAdd (i + 1) l)) (Fin.natAdd (i + 1) l)
  have hu : (facetPoint x 1 j) (Fin.natAdd (i + 1) l) = 1 :=
    facetPoint_tail x 1 l
  have e := reflect_sub_of_one
    (facetPoint x 1 j) (Fin.natAdd (i + 1) l) hu
  rw [e] at h
  exact h.symm

theorem odo_facetPoint_add_tail {i j M : ℕ} (x : Fin i → ℤ) (c' : ℤ) (t : ℕ)
    (l : Fin j) :
    odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (Fin.natAdd (i + 1) l))
      = odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) := by
  have hneq : Fin.natAdd (i + 1) l ≠ Fin.castAdd j (Fin.last i) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
    omega
  have heq : (facetPoint x 1 j) (Fin.natAdd (i + 1) l)
      = (facetPoint x 1 j) (Fin.castAdd j (Fin.last i)) := by
    rw [facetPoint_tail, facetPoint_mid]
  have h := odo_swap_coord (i + 1 + j) M c' t
    (facetPoint x 1 j + unit (Fin.natAdd (i + 1) l))
    (Fin.castAdd j (Fin.last i)) (Fin.natAdd (i + 1) l)
  have e := swap_add_eq_add (facetPoint x 1 j)
    (Fin.castAdd j (Fin.last i)) (Fin.natAdd (i + 1) l) hneq.symm heq.symm
  rw [e] at h
  calc
    odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (Fin.natAdd (i + 1) l)) =
        odo (i + 1 + j) (2 * M) (fun _ => c') t
          (facetPoint x 1 j + unit (Fin.castAdd j (Fin.last i))) := h.symm
    _ = odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) := by
      rw [facetPoint_add_mid_point x 1]
      norm_num

theorem odo_facetPoint_sub_mid {i j M : ℕ} (x : Fin i → ℤ) (c' : ℤ) (t : ℕ) :
    odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j - unit (Fin.castAdd j (Fin.last i)))
      = odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 1 j) := by
  have h := odo_reflect_coord (i + 1 + j) M c' t
    (facetPoint x 1 j - unit (Fin.castAdd j (Fin.last i)))
    (Fin.castAdd j (Fin.last i))
  have hu : (facetPoint x 1 j) (Fin.castAdd j (Fin.last i)) = 1 :=
    facetPoint_mid x 1
  have e := reflect_sub_of_one
    (facetPoint x 1 j) (Fin.castAdd j (Fin.last i)) hu
  rw [e] at h
  exact h.symm

theorem odo_facetPoint_add_mid {i j M : ℕ} (x : Fin i → ℤ) (c' : ℤ) (t : ℕ) :
    odo (i + 1 + j) (2 * M) (fun _ => c') t
        (facetPoint x 1 j + unit (Fin.castAdd j (Fin.last i)))
      = odo (i + 1 + j) (2 * M) (fun _ => c') t (facetPoint x 2 j) := by
  rw [facetPoint_add_mid_point x 1]
  norm_num

end DimRed
