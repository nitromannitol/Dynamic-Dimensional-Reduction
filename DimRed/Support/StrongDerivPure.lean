module

public import DimRed.Support.NonnegativeUpdate
public import DimRed.Support.RegInduction
public import DimRed.Support.DerivBound
public import DimRed.Support.AxisStep
public import DimRed.Support.FacetNbr
public import DimRed.Support.OneDimTerminal
public import DimRed.Support.CornerBound

@[expose] public section

/-!
# The strong derivative clause for a nonempty head

The strong derivative clause of Proposition 4.1 for a nonempty head, at every
time.  The first clause of Lemma `lem:strict-head-facet` in `dimred-corrected-arxiv.tex` (the assertion `C_t` in its proof) proves the bound
`v_t(x) - v_t(x + 2 e_k) ≤ 2 x_k` for every point of the positive orthant whose
`k`-th coordinate is not the largest, and the clause follows because the facet
point `(x_i, 1, 1_j)` has `i ≥ 1` and its `(i+1)`-st coordinate is `1 < x_1`.

The route is a floor step that
turns a bound on the neighbour sums into a bound on the odometer, applied to
four families of differences (first differences, first differences with a
one-step time shift, mixed second differences, and pure second differences off
the top coordinate), each by induction on time.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The positive orthant `{1, …, M}^d`, unsorted. -/
def inPos (d M : ℕ) (x : Site d) : Prop := ∀ l : Fin d, 1 ≤ x l ∧ x l ≤ (M : ℤ)

/-- A point of the positive orthant lies in the hypercube. -/
theorem inPos_inCube {d M : ℕ} {x : Site d} (hx : inPos d M x) : inCube d (2 * M) x := by
  intro l
  obtain ⟨h1, h2⟩ := hx l
  rw [loCoord_two_mul, hiCoord_two_mul]
  exact ⟨by omega, h2⟩

/-- A neighbour of a point of the positive orthant in a positive direction is
again in the orthant, unless the coordinate is at the top. -/
theorem inPos_add_unit_or {d M : ℕ} {x : Site d} (hx : inPos d M x) (l : Fin d) :
    inPos d M (x + unit l) ∨ x l = (M : ℤ) := by
  by_cases h : x l = (M : ℤ)
  · exact Or.inr h
  · refine Or.inl fun k => ?_
    have hk := hx k
    rw [add_unit_apply]
    by_cases hkl : k = l
    · subst hkl
      simp only []
      constructor <;> omega
    · simp only [ite_eq_right hkl, add_zero]
      exact hk

/-- A neighbour of a point of the positive orthant in a negative direction is
again in the orthant, unless the coordinate is at the bottom. -/
theorem inPos_sub_unit_or {d M : ℕ} {x : Site d} (hx : inPos d M x) (l : Fin d) :
    inPos d M (x - unit l) ∨ x l = 1 := by
  by_cases h : x l = 1
  · exact Or.inr h
  · refine Or.inl fun k => ?_
    have hk := hx k
    rw [sub_unit_apply]
    by_cases hkl : k = l
    · subst hkl
      simp only []
      constructor <;> omega
    · simp only [ite_eq_right hkl, sub_zero]
      exact hk

/-- A step above the top coordinate leaves the hypercube. -/
theorem not_inCube_add_unit_of_eq {d M : ℕ} {x : Site d} (l : Fin d) (hxl : x l = (M : ℤ)) :
    ¬ inCube d (2 * M) (x + unit l) := by
  intro hc
  have h := hc l
  rw [add_unit_self, loCoord_two_mul, hiCoord_two_mul] at h
  omega

/-- The neighbour sum of an affine function is `2d` times its value. -/
theorem nbrSum_affine {d : ℕ} (a : Fin d → ℤ) (b : ℤ) (x : Site d) :
    nbrSum (fun y => ∑ l, a l * y l + b) x = 2 * (d : ℤ) * (∑ l, a l * x l + b) := by
  simp only [nbrSum, add_unit_apply, sub_unit_apply]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A neighbour off the cube contributes at most zero. -/
theorem term_outside (d M : ℕ) (s s' : ℕ) (y w : Site d) (hy : ¬ inCube d (2 * M) y) :
    odoUnif d (2 * M) s y - odoUnif d (2 * M) s' (y + w) ≤ 0 := by
  have h1 : odoUnif d (2 * M) s y = 0 :=
    odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) s y hy
  have h2 : 0 ≤ odoUnif d (2 * M) s' (y + w) :=
    odo_nonneg d (2 * M) (fun _ => 2 * (d : ℤ)) s' (y + w)
  rw [h1]; linarith

/-- A reflected neighbour contributes the same term as the point itself. -/
theorem term_reflect (d M : ℕ) (s s' : ℕ) (x w : Site d) (l : Fin d)
    (hxl : x l = 1) (hwl : w l = 0) :
    odoUnif d (2 * M) s (x - unit l) - odoUnif d (2 * M) s' (x - unit l + w)
      = odoUnif d (2 * M) s x - odoUnif d (2 * M) s' (x + w) := by
  have h1 : odoUnif d (2 * M) s (x - unit l) = odoUnif d (2 * M) s x :=
    odo_sub_unit_of_one d M (2 * (d : ℤ)) s x l hxl
  have h2 : x - unit l + w = (x + w) - unit l := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_apply]
    by_cases hk : k = l
    · subst hk; rw [hwl]; ring
    · simp [hk]
  have h3 : (x + w) l = 1 := by rw [Pi.add_apply, hxl, hwl]; norm_num
  have h4 : odoUnif d (2 * M) s' ((x + w) - unit l) = odoUnif d (2 * M) s' (x + w) :=
    odo_sub_unit_of_one d M (2 * (d : ℤ)) s' (x + w) l h3
  rw [h1, h2, h4]

/-- The comparison rule (R) in the proof of `lem:strict-head-facet` in `dimred-corrected-arxiv.tex`: a bound on the difference of the
neighbour sums at two times gives the same bound on the odometer one step later. -/
theorem floor_step (d M : ℕ) (hd : 1 ≤ d) (s s' : ℕ) (x w : Site d)
    (hx : inCube d (2 * M) x) (hxw : inCube d (2 * M) (x + w)) (g : ℤ)
    (h : nbrSum (odoUnif d (2 * M) s) x - nbrSum (odoUnif d (2 * M) s') (x + w)
      ≤ 2 * (d : ℤ) * g) :
    odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) (s' + 1) (x + w) ≤ g := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have h' : nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x
      - nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w) ≤ 2 * (d : ℤ) * g := h
  have h1 := DimRed.bounded_point_update d (2 * M) hd (fun _ => 2 * (d : ℤ))
    (fun _ _ => by positivity) (fun _ _ => by linarith) s x hx
  have h2 := DimRed.bounded_point_update d (2 * M) hd (fun _ => 2 * (d : ℤ))
    (fun _ _ => by positivity) (fun _ _ => by linarith) s' (x + w) hxw
  have hA : (2 * (d : ℤ) + nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x)
        / (2 * (d : ℤ))
      = nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x / (2 * (d : ℤ)) + 1 := by
    rw [show 2 * (d : ℤ) + nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x
        = nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x + 2 * (d : ℤ) * 1 by ring]
    exact Int.add_mul_ediv_left _ _ (ne_of_gt hdpos)
  have hB : (2 * (d : ℤ) + nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w))
        / (2 * (d : ℤ))
      = nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w) / (2 * (d : ℤ)) + 1 := by
    rw [show 2 * (d : ℤ) + nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w)
        = nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w) + 2 * (d : ℤ) * 1 by ring]
    exact Int.add_mul_ediv_left _ _ (ne_of_gt hdpos)
  have hle := ediv_sub_ediv_le (nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x)
    (nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w)) (2 * d) (by omega)
  have hg := ediv_le_of_le_mul
    (nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x
      - nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w)) g
    (2 * d) (by omega) (by push_cast; linarith [h'])
  push_cast at hle
  have hle' : nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) x / (2 * (d : ℤ))
      - nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s') (x + w) / (2 * (d : ℤ)) ≤ g :=
    le_trans hle hg
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x
      - odo d (2 * M) (fun _ => 2 * (d : ℤ)) (s' + 1) (x + w) ≤ g
  rw [h1, h2, hA, hB]
  linarith

/-- The neighbour sum of a difference is bounded term by term. -/
theorem nbrSum_sub_le_of_terms {d : ℕ} (u u' : Site d → ℤ) (x w : Site d) (G : Site d → ℤ)
    (hG : nbrSum G x = 2 * (d : ℤ) * G x)
    (hp : ∀ l, u (x + unit l) - u' (x + unit l + w) ≤ G (x + unit l))
    (hm : ∀ l, u (x - unit l) - u' (x - unit l + w) ≤ G (x - unit l)) :
    nbrSum u x - nbrSum u' (x + w) ≤ 2 * (d : ℤ) * G x := by
  have hshift : nbrSum u' (x + w) = nbrSum (fun y => u' (y + w)) x :=
    (nbrSum_shift u' x w).symm
  have hsub : nbrSum u x - nbrSum (fun y => u' (y + w)) x
      = nbrSum (fun y => u y - u' (y + w)) x :=
    (nbrSum_sub u (fun y => u' (y + w)) x).symm
  rw [hshift, hsub, ← hG]
  simp only [nbrSum]
  rw [Finset.sum_add_distrib]
  have hstep : (∑ i : Fin d, ((u (x + unit i) - u' (x + unit i + w))
      + (u (x - unit i) - u' (x - unit i + w))))
      ≤ ∑ i : Fin d, (G (x + unit i) + G (x - unit i)) :=
    Finset.sum_le_sum fun i _ => add_le_add (hp i) (hm i)
  have hright : (∑ i : Fin d, (G (x + unit i) + G (x - unit i)))
      = 2 * (d : ℤ) * G x := by
    rw [← hG]; simp only [nbrSum]
  have hsplit : (∑ i : Fin d, ((u (x + unit i) - u' (x + unit i + w))
      + (u (x - unit i) - u' (x - unit i + w))))
      = (∑ i : Fin d, (u (x + unit i) - u' (x + unit i + w)))
        + ∑ i : Fin d, (u (x - unit i) - u' (x - unit i + w)) :=
    Finset.sum_add_distrib
  rw [hsplit] at hstep
  linarith [hstep, hright]



/-- The one-dimensional neighbour inequality `v_t(y+1) + v_t(y-1) ≤ 2v_{t+1}(y) - 1`, the analogue for the one-dimensional odometer of `NU_M ≤ KU_M - 1` in fact (c) of the proof of `lem:strict-head-facet` in `dimred-corrected-arxiv.tex`. -/
theorem oneDim_nbr_le (M t : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y) :
    odoUnif 1 (2 * M) t (y + unit 0) + odoUnif 1 (2 * M) t (y - unit 0)
      ≤ 2 * odoUnif 1 (2 * M) (t + 1) y - 1 := by
  have h := DimRed.bounded_point_update 1 (2 * M) (by omega) (fun _ => 2)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) t y hy
  simp only [nbrSum, Fin.sum_univ_one] at h
  have hq : (2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
      + odo 1 (2 * M) (fun _ => 2) t (y - unit 0))) / 2
      = odo 1 (2 * M) (fun _ => 2) (t + 1) y := by
    simpa using h.symm
  have h1 : 2 * odo 1 (2 * M) (fun _ => 2) (t + 1) y
      ≤ 2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
        + odo 1 (2 * M) (fun _ => 2) t (y - unit 0)) := by
    rw [← hq]
    have := Int.ediv_mul_le (2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
      + odo 1 (2 * M) (fun _ => 2) t (y - unit 0))) (by norm_num : (2:ℤ) ≠ 0)
    linarith
  have h2 : 2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
      + odo 1 (2 * M) (fun _ => 2) t (y - unit 0))
      < 2 * odo 1 (2 * M) (fun _ => 2) (t + 1) y + 2 := by
    rw [← hq]
    nlinarith [Int.lt_ediv_add_one_mul_self (2 + (odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
      + odo 1 (2 * M) (fun _ => 2) t (y - unit 0))) (by norm_num : (0:ℤ) < 2)]
  have key : odo 1 (2 * M) (fun _ => 2) t (y + unit 0)
      + odo 1 (2 * M) (fun _ => 2) t (y - unit 0)
      ≤ 2 * odo 1 (2 * M) (fun _ => 2) (t + 1) y - 1 := by omega
  simpa [odoUnif] using key

/-- The comparison function for the bound `v_t(x) ≤ U_M(x_k)` of fact (c) in the proof of `lem:strict-head-facet` (`dimred-corrected-arxiv.tex`): here the one-dimensional
odometer of the `l`-th coordinate at time `t`, extended by zero off the cube, whose terminal value is `U_M` (`lem:one-terminal-profile`). -/
def oneDimComp (d M : ℕ) (l : Fin d) (t : ℕ) (z : Site d) : ℤ :=
  if inCube d (2 * M) z then odoUnif 1 (2 * M) t (fun _ => z l) else 0

/-- The neighbour sum of the comparison function is bounded by the two
one-dimensional neighbour values plus `2d - 2` copies of the centre value. -/
theorem nbrSum_oneDimComp_le (d M : ℕ) (hd : 1 ≤ d) (l : Fin d) (t : ℕ) (y : Site d) :
    nbrSum (oneDimComp d M l t) y ≤
      (2 * (d : ℤ) - 2) * odoUnif 1 (2 * M) t (fun _ => y l)
        + (odoUnif 1 (2 * M) t (fun _ => y l + 1)
          + odoUnif 1 (2 * M) t (fun _ => y l - 1)) := by
  have hterm : ∀ m : Fin d, m ≠ l →
      oneDimComp d M l t (y + unit m) + oneDimComp d M l t (y - unit m) ≤
        2 * odoUnif 1 (2 * M) t (fun _ => y l) := by
    intro m hm
    have hplus : (y + unit m) l = y l := add_unit_other d y m l (fun h => hm h.symm)
    have hminus : (y - unit m) l = y l := sub_unit_other d y m l (fun h => hm h.symm)
    have hnn : (0 : ℤ) ≤ odoUnif 1 (2 * M) t (fun _ => y l) :=
      odo_nonneg 1 (2 * M) (fun _ => 2) t (fun _ => y l)
    simp only [oneDimComp]
    split_ifs with h1 h2
    · rw [hplus, hminus]; ring_nf; exact le_rfl
    · rw [hplus]; linarith
    · rw [hminus]; linarith
    · linarith
  have hl : oneDimComp d M l t (y + unit l) + oneDimComp d M l t (y - unit l) ≤
      odoUnif 1 (2 * M) t (fun _ => y l + 1)
        + odoUnif 1 (2 * M) t (fun _ => y l - 1) := by
    have h1' : (fun _ : Fin 1 => (y + unit l) l) = (fun _ => y l + 1) := by
      funext i; simp [Pi.add_apply, unit, Pi.single_eq_same]
    have h2' : (fun _ : Fin 1 => (y - unit l) l) = (fun _ => y l - 1) := by
      funext i; simp [Pi.sub_apply, unit, Pi.single_eq_same]
    have hnn1 : (0 : ℤ) ≤ odoUnif 1 (2 * M) t (fun _ => y l + 1) :=
      odo_nonneg 1 (2 * M) (fun _ => 2) t (fun _ => y l + 1)
    have hnn2 : (0 : ℤ) ≤ odoUnif 1 (2 * M) t (fun _ => y l - 1) :=
      odo_nonneg 1 (2 * M) (fun _ => 2) t (fun _ => y l - 1)
    simp only [oneDimComp]
    split_ifs with h1 h2
    · rw [h1', h2']
    · rw [h1']; linarith
    · rw [h2']; linarith
    · linarith
  simp only [nbrSum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ l)]
  have hrest : ∑ m ∈ Finset.univ.erase l,
      (oneDimComp d M l t (y + unit m) + oneDimComp d M l t (y - unit m))
      ≤ ∑ _m ∈ Finset.univ.erase l, 2 * odoUnif 1 (2 * M) t (fun _ => y l) :=
    Finset.sum_le_sum (fun m hm => hterm m (Finset.ne_of_mem_erase hm))
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
    Fintype.card_fin] at hrest
  have hd1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  simp only [nsmul_eq_mul] at hrest
  rw [hd1] at hrest
  linarith

/-- The supersolution inequality for the one-dimensional comparison function. -/
theorem odo_le_oneDim_sup (d M : ℕ) (hd : 1 ≤ d) (l : Fin d) (t : ℕ) (y : Site d)
    (hy : inCube d (2 * M) y) :
    (-(2 * (d : ℤ)) * oneDimComp d M l (t + 1) y + nbrSum (oneDimComp d M l t) y)
      + 2 * (d : ℤ) ≤ 2 * (d : ℤ) - 1 := by
  have hy1 : inCube 1 (2 * M) (fun _ : Fin 1 => y l) := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst hi
    exact hy l
  have hnb := oneDim_nbr_le M t (fun _ : Fin 1 => y l) hy1
  have h1' : (fun _ : Fin 1 => y l) + unit 0 = (fun _ => y l + 1) := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst hi
    simp [Pi.add_apply, unit, Pi.single_eq_same]
  have h2' : (fun _ : Fin 1 => y l) - unit 0 = (fun _ => y l - 1) := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst hi
    simp [Pi.sub_apply, unit, Pi.single_eq_same]
  rw [h1', h2'] at hnb
  have hsum := nbrSum_oneDimComp_le d M hd l t y
  have hmono : odoUnif 1 (2 * M) t (fun _ => y l)
      ≤ odoUnif 1 (2 * M) (t + 1) (fun _ => y l) :=
    odo_mono 1 (2 * M) (fun _ => 2) (Nat.le_succ t) _
  simp only [oneDimComp, hy, ite_true]
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hsum' : nbrSum (oneDimComp d M l t) y
      ≤ (2 * (d : ℤ) - 2) * odoUnif 1 (2 * M) t (fun _ => y l)
        + (odoUnif 1 (2 * M) t (fun _ => y l + 1)
          + odoUnif 1 (2 * M) t (fun _ => y l - 1)) := hsum
  have hstep : (2 * (d : ℤ) - 2) * odoUnif 1 (2 * M) t (fun _ => y l)
      + (odoUnif 1 (2 * M) t (fun _ => y l + 1)
        + odoUnif 1 (2 * M) t (fun _ => y l - 1))
      ≤ 2 * (d : ℤ) * odoUnif 1 (2 * M) (t + 1) (fun _ => y l) - 1 := by
    nlinarith [hmono, hnb]
  linarith

/-- Domination by the one-dimensional odometer at the same time. Since that odometer is at most its terminal value `U_M` (`lem:one-terminal-profile`), this gives the bound of fact (c) in the proof of `lem:strict-head-facet` in
`dimred-corrected-arxiv.tex`. -/
theorem odo_le_oneDim (d M : ℕ) (hd : 1 ≤ d) (l : Fin d) (t : ℕ) (x : Site d) :
    odoUnif d (2 * M) t x ≤ odoUnif 1 (2 * M) t (fun _ => x l) := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hpar := (Frozen.parabolic_comparison d (2 * M) hd (fun _ => 2 * (d : ℤ))

    (fun _ _ => by linarith)).2
  have hmain := hpar (oneDimComp d M l)
    (fun t z => by
      by_cases h : inCube d (2 * M) z
      · simp only [oneDimComp, h, ite_true]; exact odo_nonneg 1 (2 * M) (fun _ => 2) t _
      · simp only [oneDimComp, h, ite_false]; exact le_rfl)
    (fun t z hz => by simp only [oneDimComp, hz, ite_false])
    (fun t z hz => odo_le_oneDim_sup d M hd l t z hz) t x
  by_cases hx : inCube d (2 * M) x
  · simpa only [oneDimComp, hx, ite_true, odoUnif] using hmain
  · simp only [odoUnif, odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) t x hx]
    exact odo_nonneg 1 (2 * M) (fun _ => 2) t _

/-- The corner value is at most `M`, fact (c) of the proof of `lem:strict-head-facet` in `dimred-corrected-arxiv.tex`. -/
theorem odo_corner_le_M (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (t : ℕ) :
    odoUnif d (2 * M) t (cornerPoint d M) ≤ (M : ℤ) := by
  have h1 : odoUnif d (2 * M) t (cornerPoint d M) ≤ odoUnif 1 (2 * M) t (fun _ => (M : ℤ)) := by
    have h := odo_le_oneDim d M hd ⟨0, hd⟩ t (cornerPoint d M)
    simpa [cornerPoint] using h
  have h2 : odoUnif 1 (2 * M) t (fun _ => (M : ℤ)) ≤ (M : ℤ) := by
    have hle : ((odoUnif 1 (2 * M) t (fun _ => (M : ℤ))).toNat : ℕ∞) ≤
        odoInfUnif 1 (2 * M) (fun _ => (M : ℤ)) := by
      rw [odoInfUnif, odoInf]
      exact le_iSup (fun s => ((odoUnif 1 (2 * M) s (fun _ => (M : ℤ))).toNat : ℕ∞)) t
    have hy1 : (1 : ℤ) ≤ (fun _ : Fin 1 => (M : ℤ)) 0 := by
      simp only
      exact_mod_cast hM
    have hyM : (fun _ : Fin 1 => (M : ℤ)) 0 ≤ (M : ℤ) := le_rfl
    rw [odoInf_one_eq M hM (fun _ => (M : ℤ)) hy1 hyM] at hle
    have hnat := ENat.natCast_le_natCast.mp hle
    have hval : (((M : ℤ) * ((M : ℤ) + 1) - (M : ℤ) * ((M : ℤ) - 1)) / 2).toNat = M := by
      have hz : ((M : ℤ) * ((M : ℤ) + 1) - (M : ℤ) * ((M : ℤ) - 1))
          = 2 * (M : ℤ) := by ring
      rw [hz, Int.mul_ediv_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)]
      simp
    rw [hval] at hnat
    have hnn : (0 : ℤ) ≤ odoUnif 1 (2 * M) t (fun _ => (M : ℤ)) :=
      odo_nonneg 1 (2 * M) (fun _ => 2) t _
    omega
  linarith

/-- The first-difference bound, fact (c) of the proof of `lem:strict-head-facet` in `dimred-corrected-arxiv.tex`. -/
theorem odo_first_diff (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (t : ℕ) (k : Fin d)
    (x : Site d) (hxk : 1 ≤ x k) :
    odoUnif d (2 * M) t x - odoUnif d (2 * M) t (x + unit k) ≤ x k := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hcor : ∀ t : ℕ, odo d (2 * M) (fun _ => 2 * (d : ℤ)) t (cornerPoint d M)
      ≤ (1 : ℤ) * (M : ℤ) := fun t => by
    have h := odo_corner_le_M d M hd hM t
    simp only [odoUnif] at h
    simpa using h
  have h := odo_deriv_bound d M hd (2 * (d : ℤ)) (by positivity)
      (by linarith) 1 (by norm_num) hcor t k x hxk
  simp only [odoUnif] at h ⊢
  norm_num at h
  linarith

/-- The top-coordinate case of the time-shifted first difference. -/
theorem odo_time_diff_top (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s : ℕ) (k : Fin d)
    (x : Site d) (hxk : x k = (M : ℤ)) :
    odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) s (x + unit k) ≤ x k := by
  have hout : ¬ inCube d (2 * M) (x + unit k) := not_inCube_add_unit_of_eq k hxk
  have hzero : odoUnif d (2 * M) s (x + unit k) = 0 :=
    odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) s (x + unit k) hout
  have hle : odoUnif d (2 * M) (s + 1) x ≤ (M : ℤ) := by
    by_cases hx : inCube d (2 * M) x
    · have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hc := odo_le_corner d M hd (2 * (d : ℤ)) (by positivity)
        (by linarith) (s + 1) x hx k hxk
      have hM' := odo_corner_le_M d M hd hM (s + 1)
      simp only [odoUnif] at hc hM' ⊢
      linarith
    · simp only [odoUnif, odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (s + 1) x hx]
      exact Int.natCast_nonneg M
  rw [hzero, hxk]
  linarith

/-- The interior case of the time-shifted first difference, from the neighbour
bound that the floor step consumes. -/
theorem odo_time_diff_mid (d M T : ℕ) (hd : 1 ≤ d) (_hM : 1 ≤ M)
    (_hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s)
    (s : ℕ) (_hs : s + 2 ≤ T)
    (_hIH : ∀ (k : Fin d) (x : Site d), inPos d M x →
      odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) s (x + unit k) ≤ x k)
    (k : Fin d) (x : Site d) (hx : inPos d M x)
    (_hk2 : 2 ≤ x k) (_hkM : x k ≤ (M : ℤ) - 1)
    (hnbr : nbrSum (odoUnif d (2 * M) (s + 1)) x - nbrSum (odoUnif d (2 * M) s) (x + unit k)
      ≤ 2 * (d : ℤ) * x k) :
    odoUnif d (2 * M) (s + 2) x - odoUnif d (2 * M) (s + 1) (x + unit k) ≤ x k := by
  have hx' : inCube d (2 * M) x := inPos_inCube hx
  have hxw : inCube d (2 * M) (x + unit k) := by
    rcases inPos_add_unit_or hx k with h | h
    · exact inPos_inCube h
    · omega
  have hfloor := floor_step d M hd (s + 1) s x (unit k) hx' hxw (x k) hnbr
  simpa [Nat.add_assoc] using hfloor

/-- The neighbour bound of the interior case, term by term. -/
theorem odo_time_diff_mid_nbr (d M T : ℕ) (_hd : 1 ≤ d) (_hM : 1 ≤ M)
    (_hW : ∀ s, 1 ≤ s → s < T → RegWeak d M s)
    (s : ℕ) (_hs : s + 2 ≤ T)
    (hIH : ∀ (k : Fin d) (x : Site d), inPos d M x →
      odoUnif d (2 * M) (s + 1) x - odoUnif d (2 * M) s (x + unit k) ≤ x k)
    (k : Fin d) (x : Site d) (hx : inPos d M x)
    (hk2 : 2 ≤ x k) (hkM : x k ≤ (M : ℤ) - 1) :
    nbrSum (odoUnif d (2 * M) (s + 1)) x - nbrSum (odoUnif d (2 * M) s) (x + unit k)
      ≤ 2 * (d : ℤ) * x k := by
  have hG : nbrSum (fun y : Site d => y k) x = 2 * (d : ℤ) * x k := by
    have h := nbrSum_affine (fun l : Fin d => if l = k then (1 : ℤ) else 0) 0 x
    have e1 : (fun y : Site d => ∑ l : Fin d,
        (if l = k then (1 : ℤ) else 0) * y l + 0) = fun y => y k := by
      funext y
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [hb]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have e2 : (∑ l : Fin d, (if l = k then (1 : ℤ) else 0) * x l + 0) = x k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [hb]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e1, e2] at h
    exact h
  have hpos_k : inPos d M (x + unit k) := by
    intro m
    have hm := hx m
    rw [add_unit_apply]
    by_cases hmk : m = k
    · subst hmk
      rw [ite_eq_left rfl]
      constructor <;> omega
    · rw [ite_eq_right hmk, add_zero]; exact hm
  refine nbrSum_sub_le_of_terms (odoUnif d (2 * M) (s + 1)) (odoUnif d (2 * M) s)
    x (unit k) (fun y => y k) hG ?_ ?_
  · intro l
    by_cases hlk : l = k
    · subst hlk
      have hIH' := hIH l (x + unit l) hpos_k
      have hval : (x + unit l) l = x l + 1 := add_unit_self d x l
      rw [hval] at hIH' ⊢
      exact hIH'
    · have hval : (x + unit l) k = x k := add_unit_other d x l k (Ne.symm hlk)
      rcases inPos_add_unit_or hx l with h | h
      · have hIH' := hIH k (x + unit l) h
        rw [hval] at hIH' ⊢
        exact hIH'
      · have hout : ¬ inCube d (2 * M) (x + unit l) := not_inCube_add_unit_of_eq l h
        have hterm := term_outside d M (s + 1) s (x + unit l) (unit k) hout
        rw [hval]
        linarith
  · intro l
    by_cases hlk : l = k
    · subst hlk
      have hval : (x - unit l) l = x l - 1 := sub_unit_self d x l
      have hcomm : (x - unit l) + unit l = x := by abel
      have hpos' : inPos d M (x - unit l) := by
        intro m
        have hm := hx m
        rw [sub_unit_apply]
        by_cases hml : m = l
        · subst hml
          rw [ite_eq_left rfl]
          constructor <;> omega
        · rw [ite_eq_right hml, sub_zero]; exact hm
      have hIH' := hIH l (x - unit l) hpos'
      rw [hcomm, hval] at hIH' ⊢
      exact hIH'
    · have hval : (x - unit l) k = x k := sub_unit_other d x l k (Ne.symm hlk)
      rcases inPos_sub_unit_or hx l with h | h
      · have hIH' := hIH k (x - unit l) h
        rw [hval] at hIH' ⊢
        exact hIH'
      · have hwl : (unit k : Site d) l = 0 := unit_apply_ne hlk
        have hterm := term_reflect d M (s + 1) s x (unit k) l h hwl
        rw [hval]
        rw [hterm]
        have hIH' := hIH k x hx
        linarith

end DimRed
