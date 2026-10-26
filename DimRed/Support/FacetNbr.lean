module

public import DimRed.Support.AxisStep
public import DimRed.Support.Difference

@[expose] public section

/-
The coordinate evaluations and neighbour identities at a facet point
`(x_i, 1, 1_j)` from the statement labelled `base_dimension` in `dimred-corrected-arxiv.tex`.
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

/-- The mid facet point with its first tail coordinate raised from one to two:
the paper's tail neighbour `(x_i, 2, 2, 1_{j-1})` in Step 7 of the proof of `lem:strict-head-facet` in `dimred-corrected-arxiv.tex`.  When
`j = 0` the tail sum is empty and the point is the mid point itself. -/
def facetTailRaise {i : ℕ} (x : Fin i → ℤ) (j : ℕ) : Site (i + 1 + j) :=
  fun l => if i + 1 ≤ (l : ℕ) then (if (l : ℕ) = i + 1 then 2 else 1) else facetPoint x 2 j l

theorem facetTailRaise_apply {i : ℕ} (x : Fin i → ℤ) (j : ℕ) (l : Fin (i + 1 + j)) :
    facetTailRaise x j l
      = if i + 1 ≤ (l : ℕ) then (if (l : ℕ) = i + 1 then 2 else 1) else facetPoint x 2 j l := rfl

theorem facetTailRaise_eq_mid {i : ℕ} (x : Fin i → ℤ) (j : ℕ) (hj : j = 0) :
    facetTailRaise x j = facetPoint x 2 j := by
  subst hj
  funext l
  rw [facetTailRaise_apply]
  have h : ¬ (i + 1 ≤ (l : ℕ)) := by
    have := l.isLt
    omega
  rw [ite_eq_right h]

theorem facetTailRaise_head {i : ℕ} (x : Fin i → ℤ) (j : ℕ) (a : Fin i) :
    facetTailRaise x j (Fin.castAdd j (Fin.castSucc a))
      = facetPoint x 2 j (Fin.castAdd j (Fin.castSucc a)) := by
  rw [facetTailRaise_apply]
  have h : ¬ (i + 1 ≤ ((Fin.castAdd j (Fin.castSucc a) : Fin (i + 1 + j)) : ℕ)) := by
    simp only [Fin.val_castAdd, Fin.val_castSucc]
    omega
  rw [ite_eq_right h]

theorem facetTailRaise_mid {i : ℕ} (x : Fin i → ℤ) (j : ℕ) :
    facetTailRaise x j (Fin.castAdd j (Fin.last i))
      = facetPoint x 2 j (Fin.castAdd j (Fin.last i)) := by
  rw [facetTailRaise_apply]
  have h : ¬ (i + 1 ≤ ((Fin.castAdd j (Fin.last i) : Fin (i + 1 + j)) : ℕ)) := by
    simp only [Fin.val_castAdd, Fin.val_last]
    omega
  rw [ite_eq_right h]

theorem facetTailRaise_tail {i : ℕ} (x : Fin i → ℤ) (j : ℕ) (b : Fin j) :
    facetTailRaise x j (Fin.natAdd (i + 1) b)
      = if (b : ℕ) = 0 then 2 else 1 := by
  rw [facetTailRaise_apply]
  have hval : ((Fin.natAdd (i + 1) b : Fin (i + 1 + j)) : ℕ) = i + 1 + (b : ℕ) := by
    simp only [Fin.val_natAdd]
  have hlt : i + 1 ≤ ((Fin.natAdd (i + 1) b : Fin (i + 1 + j)) : ℕ) := by
    rw [hval]
    omega
  rw [ite_eq_left hlt]
  by_cases hb : (b : ℕ) = 0
  · rw [ite_eq_left (by rw [hval, hb]), ite_eq_left hb]
  · rw [ite_eq_right (by rw [hval]; omega), ite_eq_right hb]

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
    rw [ite_eq_left rfl, sub_unit_self, hu]
    norm_num
  · rw [ite_eq_right hk, sub_unit_other _ _ _ _ hk]

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

/-- The tail neighbour of `facetPoint x 2 j` in the negative direction is the
point itself, by the reflection in that coordinate. -/
theorem odo_facetPoint_two_sub_tail {i j M : ℕ} (t : ℕ) (x : Fin i → ℤ) (b : Fin j) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j - unit (Fin.natAdd (i + 1) b))
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) := by
  have h := odo_reflect_coord (i + 1 + j) M (2 * ((i + 1 + j : ℕ) : ℤ)) t
    (facetPoint x 2 j) (Fin.natAdd (i + 1) b)
  have hu : (facetPoint x 2 j) (Fin.natAdd (i + 1) b) = 1 := facetPoint_tail x 2 b
  have e : (fun k => if k = Fin.natAdd (i + 1) b then 1 - (facetPoint x 2 j) k
      else (facetPoint x 2 j) k) = facetPoint x 2 j - unit (Fin.natAdd (i + 1) b) := by
    funext k
    by_cases hk : k = Fin.natAdd (i + 1) b
    · subst hk
      rw [ite_eq_left rfl, hu, sub_unit_self, hu]
    · rw [ite_eq_right hk, sub_unit_apply, ite_eq_right hk]
      norm_num
  have hfun : (fun k => if k = Fin.natAdd (i + 1) b then 1 - (facetPoint x 2 j) k
      else (facetPoint x 2 j) k)
      = (fun k => if k = Fin.natAdd (i + 1) b then 1 - (facetPoint x 2 j) (Fin.natAdd (i + 1) b)
      else (facetPoint x 2 j) k) := by
    funext k
    by_cases hk : k = Fin.natAdd (i + 1) b
    · subst hk; rfl
    · rw [ite_eq_right hk, ite_eq_right hk]
  rw [← hfun] at h
  rw [e] at h
  exact h

/-- The positive tail neighbour of `facetPoint x 2 j` is the reflection of the
point two steps below it in that coordinate. -/
theorem odo_facetPoint_two_add_tail {i j M : ℕ} (t : ℕ) (x : Fin i → ℤ) (b : Fin j) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b))
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j - unit (Fin.natAdd (i + 1) b)
          - unit (Fin.natAdd (i + 1) b)) := by
  have h := odo_reflect_coord (i + 1 + j) M (2 * ((i + 1 + j : ℕ) : ℤ)) t
    (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) (Fin.natAdd (i + 1) b)
  have hu : (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) (Fin.natAdd (i + 1) b) = 2 := by
    rw [add_unit_self, facetPoint_tail x 2 b]
    norm_num
  have e : (fun k => if k = Fin.natAdd (i + 1) b then
      1 - (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) k
      else (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) k)
      = facetPoint x 2 j - unit (Fin.natAdd (i + 1) b) - unit (Fin.natAdd (i + 1) b) := by
    funext k
    by_cases hk : k = Fin.natAdd (i + 1) b
    · subst hk
      rw [ite_eq_left rfl, hu]
      rw [sub_unit_self, sub_unit_self, facetPoint_tail x 2 b]
      norm_num
    · rw [ite_eq_right hk, sub_unit_apply, ite_eq_right hk, sub_unit_apply, ite_eq_right hk]
      rw [add_unit_other _ _ _ _ hk]
      norm_num
  have hfun : (fun k => if k = Fin.natAdd (i + 1) b then
      1 - (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) k
      else (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) k)
      = (fun k => if k = Fin.natAdd (i + 1) b then
      1 - (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) (Fin.natAdd (i + 1) b)
      else (facetPoint x 2 j + unit (Fin.natAdd (i + 1) b)) k) := by
    funext k
    by_cases hk : k = Fin.natAdd (i + 1) b
    · subst hk; rfl
    · rw [ite_eq_right hk, ite_eq_right hk]
  rw [← hfun] at h
  rw [e] at h
  exact h.symm

/-- The mid neighbour of `facetPoint x c j` in the negative direction. -/
theorem facetPoint_sub_mid_point {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) :
    facetPoint x c j - unit (Fin.castAdd j (Fin.last i)) = facetPoint x (c - 1) j := by
  rw [eq_comm, eq_sub_iff_add_eq, facetPoint_add_mid_point x (c - 1)]
  congr 1
  ring

/-- Adding a head unit vector to `facetPoint x c j` shifts `x`. -/
theorem facetPoint_add_head' {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) (a : Fin i) :
    facetPoint x c j + unit (Fin.castAdd j (Fin.castSucc a))
      = facetPoint (x + unit a) c j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · simp [facetPoint]
      apply unit_apply_ne
      intro hh
      exact Fin.castSucc_ne_last a (Fin.castAdd_injective _ _ hh.symm)
    · by_cases hab : b = a
      · subst hab; simp [facetPoint, unit_apply_self]
      · simp [facetPoint]
        rw [unit_apply_ne]
        · exact (unit_apply_ne hab).symm
        · intro hh
          exact hab (Fin.castSucc_injective _ (Fin.castAdd_injective _ _ hh))
  · intro b
    simp [facetPoint]
    apply unit_apply_ne
    intro hh
    have hv := congrArg Fin.val hh
    simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
    omega

/-- Subtracting a head unit vector from `facetPoint x c j` shifts `x`. -/
theorem facetPoint_sub_head' {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) (a : Fin i) :
    facetPoint x c j - unit (Fin.castAdd j (Fin.castSucc a))
      = facetPoint (x - unit a) c j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · simp [facetPoint]
      apply unit_apply_ne
      intro hh
      exact Fin.castSucc_ne_last a (Fin.castAdd_injective _ _ hh.symm)
    · by_cases hab : b = a
      · subst hab; simp [facetPoint, unit_apply_self]
      · simp [facetPoint]
        rw [unit_apply_ne]
        · exact (unit_apply_ne hab).symm
        · intro hh
          exact hab (Fin.castSucc_injective _ (Fin.castAdd_injective _ _ hh))
  · intro b
    simp [facetPoint]
    apply unit_apply_ne
    intro hh
    have hv := congrArg Fin.val hh
    simp [Fin.castAdd, Fin.natAdd, Fin.castLE] at hv
    omega

/-- The head part of the neighbour sum at `facetPoint x 2 j`. -/
theorem sum_head_facetPoint_two {i j M : ℕ} (t : ℕ) (x : Fin i → ℤ) :
    (∑ a : Fin (i + 1),
        (odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j + unit (Fin.castAdd j a))
          + odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j - unit (Fin.castAdd j a))))
      = (∑ a : Fin i,
          (odoUnif (i + 1 + j) (2 * M) t (facetPoint (x + unit a) 2 j)
            + odoUnif (i + 1 + j) (2 * M) t (facetPoint (x - unit a) 2 j)))
        + (odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
            + odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j)) := by
  rw [Fin.sum_univ_castSucc]
  rw [facetPoint_add_mid_point x 2, facetPoint_sub_mid_point x 2]
  norm_num
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [facetPoint_add_head' x 2 a, facetPoint_sub_head' x 2 a]
  · ring

/-- Splitting a sum over `Fin (i + 1 + j)` into the head, the mid coordinate and
the tail. -/
theorem sum_univ_head_mid_tail (i j : ℕ) (f : Fin (i + 1 + j) → ℤ) :
    (∑ k : Fin (i + 1 + j), f k)
      = (∑ a : Fin i, f (Fin.castAdd j (Fin.castSucc a)))
        + f (Fin.castAdd j (Fin.last i))
        + (∑ b : Fin j, f (Fin.natAdd (i + 1) b)) := by
  have hcast : (i + 1) + j = i + 1 + j := by omega
  have h1 : (∑ k : Fin (i + 1 + j), f k)
      = ∑ k : Fin ((i + 1) + j), f (Fin.cast hcast k) := by
    exact Fintype.sum_equiv (finCongr hcast) _ _ (fun _ => rfl)
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_castSucc]
  have e1 : ∀ a : Fin i, Fin.cast hcast (Fin.castAdd j a.castSucc)
      = Fin.castAdd j (Fin.castSucc a) := fun a => Fin.ext rfl
  have e2 : Fin.cast hcast (Fin.castAdd j (Fin.last i)) = Fin.castAdd j (Fin.last i) := Fin.ext rfl
  have e3 : ∀ b : Fin j, Fin.cast hcast (Fin.natAdd (i + 1) b) = Fin.natAdd (i + 1) b :=
    fun b => Fin.ext rfl
  simp only [e1, e2, e3]

theorem facetPoint_two_add_head {j : ℕ} (c : ℤ) :
    facetPoint ((fun _ : Fin 1 => (2 : ℤ)) + unit (0 : Fin 1)) c j
      = facetPoint (fun _ : Fin 1 => (3 : ℤ)) c j := by
  rw [← facetPoint_add_head']
  funext l
  refine Fin.addCases ?_ ?_ l
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · rw [Pi.add_apply, facetPoint_mid, facetPoint_mid]
      have hne : (Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j))
          ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
        omega
      rw [unit, Pi.single_apply, ite_eq_right hne, add_zero]
    · rw [Pi.add_apply, facetPoint_head, facetPoint_head]
      have hb : (b : ℕ) < 1 := b.isLt
      have hba : b = (0 : Fin 1) := Fin.ext (by omega)
      rw [hba, unit, Pi.single_apply, ite_eq_left rfl]
      norm_num
  · intro b
    rw [Pi.add_apply, facetPoint_tail, facetPoint_tail]
    have hne : (Fin.natAdd (1 + 1) b : Fin (1 + 1 + j))
        ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
      intro hh
      have hv := congrArg Fin.val hh
      simp [Fin.castAdd, Fin.natAdd] at hv
    rw [unit, Pi.single_apply, ite_eq_right hne]
    norm_num
theorem facetPoint_two_sub_head {j : ℕ} (c : ℤ) :
    facetPoint ((fun _ : Fin 1 => (2 : ℤ)) - unit (0 : Fin 1)) c j
      = facetPoint (fun _ : Fin 1 => (1 : ℤ)) c j := by
  rw [← facetPoint_sub_head']
  funext l
  refine Fin.addCases ?_ ?_ l
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · rw [Pi.sub_apply, facetPoint_mid, facetPoint_mid]
      have hne : (Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j))
          ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
        omega
      rw [unit, Pi.single_apply, ite_eq_right hne, sub_zero]
    · rw [Pi.sub_apply, facetPoint_head, facetPoint_head]
      have hb : (b : ℕ) < 1 := b.isLt
      have hba : b = (0 : Fin 1) := Fin.ext (by omega)
      rw [hba, unit, Pi.single_apply, ite_eq_left rfl]
      norm_num
  · intro b
    rw [Pi.sub_apply, facetPoint_tail, facetPoint_tail]
    have hne : (Fin.natAdd (1 + 1) b : Fin (1 + 1 + j))
        ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
      intro hh
      have hv := congrArg Fin.val hh
      simp [Fin.castAdd, Fin.natAdd] at hv
    rw [unit, Pi.single_apply, ite_eq_right hne, sub_zero]

theorem facetPoint_one_add_head {j : ℕ} :
    facetPoint (fun _ : Fin 1 => (1 : ℤ)) 1 j
        + unit (Fin.castAdd j (Fin.castSucc (0 : Fin 1)))
      = facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j := by
  rw [facetPoint_add_head']
  funext l
  refine Fin.addCases ?_ ?_ l
  · intro h
    refine Fin.lastCases ?_ (fun b => ?_) h
    · rw [facetPoint_mid]
      have hne : (Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j))
          ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_last] at hv
        omega
      simp only [facetPoint_mid]
    · rw [facetPoint_head]
      have hb : (b : ℕ) < 1 := b.isLt
      have hba : b = (0 : Fin 1) := Fin.ext (by omega)
      rw [hba, Pi.add_apply, facetPoint_head]
      simp [unit]
  · intro b
    rw [facetPoint_tail]
    have hne : (Fin.natAdd (1 + 1) b : Fin (1 + 1 + j))
        ≠ Fin.castAdd j (Fin.castSucc (0 : Fin 1)) := by
      intro hh
      have hv := congrArg Fin.val hh
      simp [Fin.castAdd, Fin.natAdd] at hv
    simp only [facetPoint_tail]
end DimRed
