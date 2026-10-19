import DimRed.Support.Basic

/-
The coordinate and simplex identities for appending a trailing coordinate,
`dimred-corrected-arxiv.tex`.
-/
namespace DimRed

open LatticeProb

theorem snoc_apply_castSucc {d : ℕ} (x : Site d) (c : ℤ) (a : Fin d) :
    (Fin.snoc x c : Site (d + 1)) (Fin.castSucc a) = x a := by
  exact Fin.snoc_castSucc (n := d) (α := fun _ : Fin (d + 1) => ℤ) c x a

theorem snoc_apply_last {d : ℕ} (x : Site d) (c : ℤ) :
    (Fin.snoc x c : Site (d + 1)) (Fin.last d) = c := by
  exact Fin.snoc_last (n := d) (α := fun _ : Fin (d + 1) => ℤ) c x

theorem snoc_add_unit {d : ℕ} (x : Site d) (c : ℤ) (a : Fin d) :
    Fin.snoc (x + unit a) c = Fin.snoc x c + unit (Fin.castSucc a) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [unit]
  · by_cases h : i = a
    · subst h; simp [unit]
    · have h' : (i.castSucc : Fin (d + 1)) ≠ Fin.castSucc a := by
        intro he
        exact h (Fin.castSucc_injective d he)
      simp [unit, h, h']

theorem snoc_sub_unit {d : ℕ} (x : Site d) (c : ℤ) (a : Fin d) :
    Fin.snoc (x - unit a) c = Fin.snoc x c - unit (Fin.castSucc a) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [unit]
  · by_cases h : i = a
    · subst h; simp [unit]
    · have h' : (i.castSucc : Fin (d + 1)) ≠ Fin.castSucc a := by
        intro he
        exact h (Fin.castSucc_injective d he)
      simp [unit, h, h']

theorem snoc_add_unit_last {d : ℕ} (x : Site d) (c : ℤ) :
    Fin.snoc x (c + 1) = Fin.snoc x c + unit (Fin.last d) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [unit]
  · simp [unit]

theorem snoc_sub_unit_last {d : ℕ} (x : Site d) (c : ℤ) :
    Fin.snoc x (c - 1) = Fin.snoc x c - unit (Fin.last d) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [unit]
  · simp [unit]

theorem inSimplex_snoc {d M : ℕ} (x : Site d) (c : ℤ) :
    inSimplex (d + 1) M (Fin.snoc x c) ↔
      inSimplex d M x ∧ 1 ≤ c ∧ c ≤ (M : ℤ) ∧ ∀ a : Fin d, c ≤ x a := by
  constructor
  · intro h
    have hfirst : inSimplex d M x := by
      constructor
      · intro a
        simpa only [Fin.snoc_castSucc] using h.1 (Fin.castSucc a)
      · intro a b hab
        have hab' : (Fin.castSucc a : Fin (d + 1)) ≤ Fin.castSucc b := by
          change (a : ℕ) ≤ b
          exact hab
        simpa only [Fin.snoc_castSucc] using h.2 _ _ hab'
    have hc1 := (h.1 (Fin.last d)).1
    have hcM := (h.1 (Fin.last d)).2
    have htail : ∀ a : Fin d, c ≤ x a := by
      intro a
      have hab : (Fin.castSucc a : Fin (d + 1)) ≤ Fin.last d :=
        le_of_lt (Fin.castSucc_lt_last a)
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h.2 _ _ hab
    exact ⟨hfirst, by simpa only [Fin.snoc_last] using hc1,
      by simpa only [Fin.snoc_last] using hcM, htail⟩
  · rintro ⟨hx, hc1, hcM, htail⟩
    constructor
    · intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · simpa only [Fin.snoc_last] using (show (1 : ℤ) ≤ c ∧ c ≤ (M : ℤ) from
          ⟨hc1, hcM⟩)
      · simpa only [Fin.snoc_castSucc] using hx.1 i
    · intro a b hab
      refine Fin.lastCases
        (motive := fun a : Fin (d + 1) => ∀ b : Fin (d + 1), a ≤ b →
          (Fin.snoc x c : Site (d + 1)) b ≤ (Fin.snoc x c : Site (d + 1)) a)
        (fun b hab => ?_) (fun i b hab => ?_) a b hab
      · refine Fin.lastCases
          (motive := fun b : Fin (d + 1) => Fin.last d ≤ b →
            (Fin.snoc x c : Site (d + 1)) b ≤ (Fin.snoc x c : Site (d + 1)) (Fin.last d))
          (fun _ => ?_) (fun j hbj => ?_) b hab
        · exact le_rfl
        · exfalso
          exact (not_le_of_gt (Fin.castSucc_lt_last j)) hbj
      · refine Fin.lastCases
          (motive := fun b : Fin (d + 1) => (Fin.castSucc i : Fin (d + 1)) ≤ b →
            (Fin.snoc x c : Site (d + 1)) b ≤ (Fin.snoc x c : Site (d + 1)) (Fin.castSucc i))
          (fun _ => ?_) (fun j hij => ?_) b hab
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using htail i
        · have hab' : i ≤ j := by
            change (i : ℕ) ≤ j
            exact hij
          simpa only [Fin.snoc_castSucc] using hx.2 i j hab'

theorem inSimplex_snoc_one {d M : ℕ} (hM : 1 ≤ M) (x : Site d) :
    inSimplex (d + 1) M (Fin.snoc x 1) ↔ inSimplex d M x := by
  rw [inSimplex_snoc]
  constructor
  · rintro ⟨hx, _, _, _⟩
    exact hx
  · intro hx
    refine ⟨hx, le_rfl, ?_, ?_⟩
    · exact_mod_cast hM
    · intro a
      exact (hx.1 a).1

theorem inCube_snoc {d N : ℕ} (x : Site d) (c : ℤ) :
    inCube (d + 1) N (Fin.snoc x c) ↔
      inCube d N x ∧ loCoord N ≤ c ∧ c ≤ hiCoord N := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a
      simpa only [Fin.snoc_castSucc] using h (Fin.castSucc a)
    · simpa only [Fin.snoc_last] using (h (Fin.last d)).1
    · simpa only [Fin.snoc_last] using (h (Fin.last d)).2
  · rintro ⟨hx, hc0, hc1⟩ a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa only [Fin.snoc_last] using (show loCoord N ≤ c ∧ c ≤ hiCoord N from
        ⟨hc0, hc1⟩)
    · simpa only [Fin.snoc_castSucc] using hx i

theorem nbrSum_snoc {d : ℕ} (u : Site (d + 1) → ℤ) (x : Site d) (c : ℤ) :
    nbrSum u (Fin.snoc x c) =
      (∑ i : Fin d,
        (u (Fin.snoc x c + unit (Fin.castSucc i))
          + u (Fin.snoc x c - unit (Fin.castSucc i))))
        + u (Fin.snoc x c + unit (Fin.last d))
        + u (Fin.snoc x c - unit (Fin.last d)) := by
  simp only [nbrSum, Fin.sum_univ_castSucc]
  ring

theorem facetPoint_zero {i : ℕ} (x : Fin i → ℤ) (c : ℤ) :
    facetPoint x c 0 = Fin.snoc x c := by
  unfold facetPoint
  funext k
  simpa using (Fin.append_left (Fin.snoc x c) (fun _ : Fin 0 => (1 : ℤ)) k)

theorem facetPoint_succ {i j : ℕ} (x : Fin i → ℤ) (c : ℤ) :
    facetPoint x c (j + 1) = Fin.snoc (facetPoint x c j) 1 := by
  have hone : (fun _ : Fin (j + 1) => (1 : ℤ)) =
      Fin.snoc (fun _ : Fin j => (1 : ℤ)) 1 := by
    funext k
    refine Fin.lastCases ?_ (fun _ => ?_) k <;> simp
  rw [facetPoint, hone, Fin.append_snoc]
  rfl

end DimRed
