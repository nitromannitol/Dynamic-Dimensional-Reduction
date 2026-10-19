/-
The strong topple control step of the joint induction, `dimred.tex:1036-1105`
(`d = 1`) and `dimred.tex:1447-1474` (`d ≥ 2`).
-/
import DimRed.Support.RegInduction
import DimRed.Support.OneDimConsistAll
import DimRed.Support.CornerReaches
import DimRed.Support.OneStep
import DimRed.Support.SimplexFold
import DimRed.Support.FoldIdentity
import DimRed.Support.ReflectShift
import DimRed.Support.ToppleTimeScale
import DimRed.Support.SnocSimplex
import DimRed.Support.NonnegativeUpdate
import DimRed.Frozen.Prelim.AxisMonotonicity
import DimRed.Frozen.Prelim.ParabolicComparison
import DimRed.Frozen.Prelim.ToppleLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

/-! ### The shift `y ↦ y - 1` between the scales `M` and `M - 1` -/

theorem inCube_two_mul_sub_one_iff {d M : ℕ} (hM : 2 ≤ M) (y : Site d) (hy : ∀ i, 2 ≤ y i) :
    inCube d (2 * M) y ↔ inCube d (2 * (M - 1)) (fun i => y i - 1) := by
  have hc : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  unfold inCube
  rw [loCoord_two_mul, hiCoord_two_mul, loCoord_two_mul, hiCoord_two_mul, hc]
  constructor
  · intro h i
    have h1 := h i
    have h2 := hy i
    dsimp only
    constructor <;> omega
  · intro h i
    have h1 := h i
    have h2 := hy i
    dsimp only at h1
    constructor <;> omega

/-- One step of the parallel toppling rule transfers the identity
`v^{(M)}(y) = v^{(M-1)}(y - 1)` from the point and its neighbour sum. -/
theorem odoUnif_succ_shift_of_nbrSum {d M s : ℕ} (hM : 2 ≤ M) (y : Site d) (hy : ∀ i, 2 ≤ y i)
    (h0 : odoUnif d (2 * M) s y = odoUnif d (2 * (M - 1)) s (fun i => y i - 1))
    (hn : nbrSum (odoUnif d (2 * M) s) y =
      nbrSum (odoUnif d (2 * (M - 1)) s) (fun i => y i - 1)) :
    odoUnif d (2 * M) (s + 1) y = odoUnif d (2 * (M - 1)) (s + 1) (fun i => y i - 1) := by
  have hc := inCube_two_mul_sub_one_iff hM y hy
  have hn' : nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) s) y =
      nbrSum (odo d (2 * (M - 1)) (fun _ => 2 * (d : ℤ)) s) (fun i => y i - 1) := hn
  simp only [odoUnif] at h0 ⊢
  simp only [odo, lap]
  by_cases hin : inCube d (2 * M) y
  · rw [if_pos hin, if_pos (hc.mp hin)]
    simp only [h0, hn']
    rfl
  · rw [if_neg hin, if_neg (fun h => hin (hc.mpr h))]

/-- The self-similarity identity at scale `M` against `M - 1`, on every point of
`ℤ^d` with all coordinates at least two, from its form on the sorted domain. -/
theorem selfsim_shift_of_simplex {d M s : ℕ} (hM : 2 ≤ M)
    (hC : ∀ x : Site d, inSimplex d M x → (∀ i, 1 < x i) →
      odoUnif d (2 * M) s x = odoUnif d (2 * (M - 1)) s (fun i => x i - 1))
    (y : Site d) (hy : ∀ i, 2 ≤ y i) :
    odoUnif d (2 * M) s y = odoUnif d (2 * (M - 1)) s (fun i => y i - 1) := by
  by_cases hc : inCube d (2 * M) y
  · have h1 := odoUnif_toSimplexPoint d M s y
    have h2 := odoUnif_toSimplexPoint_sub d M s y (fun k => by linarith [hy k])
    have hmem := inSimplex_toSimplexPoint d M y hc
    have hgt := gt_one_toSimplexPoint_of_gt_one d M y (fun k => by linarith [hy k])
    rw [← h1, ← h2]
    exact hC _ hmem hgt
  · have hc' : ¬ inCube d (2 * (M - 1)) (fun i => y i - 1) := by
      rwa [← inCube_two_mul_sub_one_iff hM y hy]
    simp only [odoUnif]
    rw [odo_eq_zero_outside _ _ _ _ _ hc, odo_eq_zero_outside _ _ _ _ _ hc']

/-- The self-similarity clause with `j = M - 1`, in the shifted form. -/
theorem selfsim_shift_simplex_of_regConsist {d M s : ℕ} (hM : 2 ≤ M) (hC : RegConsist d M s)
    (hs : (s : ℕ∞) ≤ toppleTime d (M - 1)) :
    ∀ x : Site d, inSimplex d M x → (∀ i, 1 < x i) →
      odoUnif d (2 * M) s x = odoUnif d (2 * (M - 1)) s (fun i => x i - 1) := by
  intro x hx hgt
  have hc : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  have h := hC (M - 1) (by omega) (by omega) hs x hx (fun i => by
    rw [hc]; linarith [hgt i])
  rw [h]
  congr 1
  funext i
  rw [hc]
  ring

/-- The identity at time `s + 1` at a point with all coordinates at least two,
from the identity at time `s` on that region and the reflecting boundary
identity at the coordinates equal to two. -/
theorem selfsim_shift_succ_of_reflect {d M s : ℕ} (hM : 2 ≤ M)
    (hC : ∀ y : Site d, (∀ i, 2 ≤ y i) →
      odoUnif d (2 * M) s y = odoUnif d (2 * (M - 1)) s (fun i => y i - 1))
    (y : Site d) (hy : ∀ i, 2 ≤ y i)
    (hrefl : ∀ k, y k = 2 → odoUnif d (2 * M) s (y - unit k) = odoUnif d (2 * M) s y) :
    odoUnif d (2 * M) (s + 1) y = odoUnif d (2 * (M - 1)) (s + 1) (fun i => y i - 1) := by
  refine odoUnif_succ_shift_of_nbrSum hM y hy (hC y hy) ?_
  simp only [nbrSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hplus : odoUnif d (2 * M) s (y + unit i) =
      odoUnif d (2 * (M - 1)) s ((fun k => y k - 1) + unit i) := by
    rw [← sub_one_add_unit]
    refine hC _ (fun k => ?_)
    by_cases hk : k = i
    · subst hk; rw [add_unit_self]; linarith [hy k]
    · rw [add_unit_other _ _ _ _ hk]; exact hy k
  have hminus : odoUnif d (2 * M) s (y - unit i) =
      odoUnif d (2 * (M - 1)) s ((fun k => y k - 1) - unit i) := by
    rw [← sub_one_sub_unit]
    by_cases h2 : y i = 2
    · rw [hrefl i h2, odoUnif_sub_unit_shift_eq d M s y i h2]
      exact hC y hy
    · refine hC _ (fun k => ?_)
      by_cases hk : k = i
      · subst hk; rw [sub_unit_self]; have := hy k; omega
      · rw [sub_unit_other _ _ _ _ hk]; exact hy k
  rw [hplus, hminus]

/-! ### One-dimensional facts -/

theorem constSite_one_add_unit (c : ℤ) :
    (fun _ : Fin 1 => c) + unit 0 = fun _ : Fin 1 => c + 1 := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  simp [unit]

theorem constSite_one_sub_unit (c : ℤ) :
    (fun _ : Fin 1 => c) - unit 0 = fun _ : Fin 1 => c - 1 := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  simp [unit]

theorem nbrSum_constSite_one (u : Site 1 → ℤ) (c : ℤ) :
    nbrSum u (fun _ : Fin 1 => c) = u (fun _ => c + 1) + u (fun _ => c - 1) := by
  rw [nbrSum, Fin.sum_univ_one, constSite_one_add_unit, constSite_one_sub_unit]

/-- The reflection `0 ↦ 1` of the cube of side `2M`. -/
theorem odoUnif_dim_one_zero_eq_one (M s : ℕ) :
    odoUnif 1 (2 * M) s (fun _ => (0 : ℤ)) = odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) := by
  have h := odo_reflect_coord 1 M (2 * ((1 : ℕ) : ℤ)) s (fun _ => (1 : ℤ)) 0
  have he : (fun k : Fin 1 => if k = 0 then 1 - (fun _ : Fin 1 => (1 : ℤ)) 0
      else (fun _ : Fin 1 => (1 : ℤ)) k) = fun _ => (0 : ℤ) := by
    funext k
    rw [if_pos (Fin.eq_zero k)]
    norm_num
  rw [he] at h
  exact h

theorem inCube_constSite_one_iff (M : ℕ) (c : ℤ) :
    inCube 1 (2 * M) (fun _ => c) ↔ 1 - (M : ℤ) ≤ c ∧ c ≤ (M : ℤ) := by
  unfold inCube
  rw [loCoord_two_mul, hiCoord_two_mul]
  constructor
  · intro h; exact h 0
  · intro h _; exact h

/-- The one-dimensional toppling rule at the point `1`. -/
theorem odoUnif_dim_one_succ_at_one (M s : ℕ) (hM : 1 ≤ M) :
    odoUnif 1 (2 * M) (s + 1) (fun _ => (1 : ℤ)) =
      odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) +
        (if odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) ≤
          odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) then 1 else 0) := by
  have hin : inCube 1 (2 * M) (fun _ => (1 : ℤ)) := by
    rw [inCube_constSite_one_iff]; constructor <;> omega
  have hz := odoUnif_dim_one_zero_eq_one M s
  have hnb := nbrSum_constSite_one (odoUnif 1 (2 * M) s) 1
  have hnb' : nbrSum (odo 1 (2 * M) (fun _ => 2 * ((1 : ℕ) : ℤ)) s) (fun _ => (1 : ℤ)) =
      odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) + odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) := by
    have e : nbrSum (odo 1 (2 * M) (fun _ => 2 * ((1 : ℕ) : ℤ)) s) (fun _ => (1 : ℤ)) =
        nbrSum (odoUnif 1 (2 * M) s) (fun _ => (1 : ℤ)) := rfl
    rw [e, hnb]
    norm_num
    rw [hz]
  change odo 1 (2 * M) (fun _ => 2 * ((1 : ℕ) : ℤ)) (s + 1) (fun _ => (1 : ℤ)) = _
  rw [odo_succ_eq _ _ _ _ _ hin]
  have hsd : sandp 1 (2 * M) (fun _ => 2 * ((1 : ℕ) : ℤ)) s (fun _ => (1 : ℤ)) =
      2 + (odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) - odoUnif 1 (2 * M) s (fun _ => (1 : ℤ))) := by
    simp only [sandp, lap]
    rw [hnb']
    change 2 * ((1 : ℕ) : ℤ) + (-(2 * ((1 : ℕ) : ℤ)) * odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) +
      (odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) + odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)))) = _
    push_cast
    ring
  rw [hsd]
  change odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) + _ = _
  split_ifs with h1 h2 h2 <;> push_cast at h1 <;> omega

/-- Axis monotonicity at the point `1` in one dimension. -/
theorem odoUnif_dim_one_two_le_one (M s : ℕ) (hM : 2 ≤ M) :
    odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) ≤ odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; exact le_refl _
  have hx : inSimplex 1 M (fun _ => (1 : ℤ)) := by
    refine ⟨fun _ => ⟨le_refl _, show (1 : ℤ) ≤ (M : ℤ) by exact_mod_cast (by omega : 1 ≤ M)⟩,
      fun _ _ _ => le_refl _⟩
  have he : (fun _ : Fin 1 => (1 : ℤ)) + unit 0 - ∑ j ∈ (∅ : Finset (Fin 1)), unit j =
      fun _ => (2 : ℤ) := by
    rw [Finset.sum_empty, sub_zero, constSite_one_add_unit]; norm_num
  have hmem : inSimplex 1 M ((fun _ : Fin 1 => (1 : ℤ)) + unit 0 -
      ∑ j ∈ (∅ : Finset (Fin 1)), unit j) := by
    rw [he]
    refine ⟨fun _ => ⟨by norm_num, show (2 : ℤ) ≤ (M : ℤ) by exact_mod_cast hM⟩,
      fun _ _ _ => le_refl _⟩
  have h := Frozen.axis_monotonicity 1 M (le_refl 1) (2 * ((1 : ℕ) : ℤ))
    s hs (fun _ => (1 : ℤ)) hx 0 ∅ (by simp) (by simp) hmem
  rw [he] at h
  exact h

/-- The first difference at the point `1` is at most one in one dimension. -/
theorem odoUnif_dim_one_one_le_two_add_one (M s : ℕ) (hM : 2 ≤ M) :
    odoUnif 1 (2 * M) s (fun _ => (1 : ℤ)) ≤ odoUnif 1 (2 * M) s (fun _ => (2 : ℤ)) + 1 := by
  induction s with
  | zero => simp [odoUnif, odo]
  | succ n ih =>
    have hr := odoUnif_dim_one_succ_at_one M n (by omega)
    have hb := odo_succ_sub_bounds 1 (2 * M) (fun _ => 2 * ((1 : ℕ) : ℤ)) n (fun _ => (2 : ℤ))
    have hmono := odoUnif_dim_one_two_le_one M n hM
    change 0 ≤ odoUnif 1 (2 * M) (n + 1) (fun _ => (2 : ℤ)) -
        odoUnif 1 (2 * M) n (fun _ => (2 : ℤ)) ∧ _ at hb
    rw [hr]
    split_ifs with h <;> omega

/-- The neighbour lemma behind `dimred.tex:1049-1051`: a site that rises by two
over two steps has a neighbour that rose by two one step earlier. -/
theorem odoUnif_dim_one_rise_two_nbr (M s : ℕ) (hs : 1 ≤ s) (c : ℤ)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (s + 2) (fun _ => c) - odoUnif 1 (2 * M) s (fun _ => c)) :
    2 ≤ odoUnif 1 (2 * M) (s + 1) (fun _ => c + 1) -
        odoUnif 1 (2 * M) (s - 1) (fun _ => c + 1) ∨
      2 ≤ odoUnif 1 (2 * M) (s + 1) (fun _ => c - 1) -
        odoUnif 1 (2 * M) (s - 1) (fun _ => c - 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  by_cases hin : inCube 1 (2 * M) (fun _ => c)
  · have hp := DimRed.bounded_point_update 1 (2 * M) (le_refl 1) (fun _ => 2 * ((1 : ℕ) : ℤ))
      (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    have hA := hp (s + 1) (fun _ => c) hin
    have hB := hp (s - 1) (fun _ => c) hin
    rw [show s - 1 + 1 = s by omega] at hB
    rw [nbrSum_constSite_one] at hA hB
    change odoUnif 1 (2 * M) (s + 2) (fun _ => c) = (2 * ((1 : ℕ) : ℤ) +
      (odoUnif 1 (2 * M) (s + 1) (fun _ => c + 1) + odoUnif 1 (2 * M) (s + 1) (fun _ => c - 1)))
        / (2 * ((1 : ℕ) : ℤ)) at hA
    change odoUnif 1 (2 * M) s (fun _ => c) = (2 * ((1 : ℕ) : ℤ) +
      (odoUnif 1 (2 * M) (s - 1) (fun _ => c + 1) + odoUnif 1 (2 * M) (s - 1) (fun _ => c - 1)))
        / (2 * ((1 : ℕ) : ℤ)) at hB
    push_cast at hA hB
    omega
  · have h0 : ∀ r, odoUnif 1 (2 * M) r (fun _ => c) = 0 := fun r =>
      odo_eq_zero_outside _ _ _ _ _ hin
    rw [h0, h0] at hbad
    omega

theorem odoUnif_le_succ_le_add_one (d N t : ℕ) (x : Site d) :
    odoUnif d N t x ≤ odoUnif d N (t + 1) x ∧ odoUnif d N (t + 1) x ≤ odoUnif d N t x + 1 := by
  have h := odo_succ_sub_bounds d N (fun _ => 2 * (d : ℤ)) t x
  simp only [odoUnif]
  constructor <;> linarith [h.1, h.2]

/-! ### The one-dimensional step at the topple time `T = τ_{M-1}`

The hypotheses `hC`, `hC'` are self-similarity at times `T` and `T - 1`, and `hW`
is strong topple control at scale `M - 1` from `T - 1`. -/

section OneDimAt

variable {M T : ℕ}

/-- A point `c ≥ 3` cannot rise by two between `T - 1` and `T + 1`. -/
theorem topple_one_dim_y3 (hM : 2 ≤ M)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1)
    (c : ℤ) (hc : 3 ≤ c)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (T + 1) (fun _ => c) -
      odoUnif 1 (2 * M) (T - 1) (fun _ => c)) : False := by
  by_cases hcM : c ≤ (M : ℤ)
  · have h1 : odoUnif 1 (2 * M) (T + 1) (fun _ => c) =
        odoUnif 1 (2 * (M - 1)) (T + 1) (fun _ => c - 1) :=
      selfsim_shift_succ_of_reflect hM hC (fun _ => c) (fun _ => by omega)
        (fun _ hk => absurd hk (by omega))
    have h2 : odoUnif 1 (2 * M) (T - 1) (fun _ => c) =
        odoUnif 1 (2 * (M - 1)) (T - 1) (fun _ => c - 1) :=
      hC' (fun _ => c) (fun _ => by omega)
    have hz : inSimplex 1 (M - 1) (fun _ => c - 1) := by
      refine ⟨fun _ => ⟨show (1 : ℤ) ≤ c - 1 by omega, ?_⟩, fun _ _ _ => le_refl _⟩
      show c - 1 ≤ ((M - 1 : ℕ) : ℤ)
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      push_cast
      omega
    have h3 := hW _ hz
    rw [h1, h2] at hbad
    omega
  · have hout : ¬ inCube 1 (2 * M) (fun _ => c) := by
      rw [inCube_constSite_one_iff]; omega
    have h0 : ∀ r, odoUnif 1 (2 * M) r (fun _ => c) = 0 := fun r =>
      odo_eq_zero_outside _ _ _ _ _ hout
    rw [h0, h0] at hbad
    omega

/-- The point `2` cannot rise by two between `T - 1` and `T + 1`. -/
theorem topple_one_dim_y2 (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (T + 1) (fun _ => (2 : ℤ)) -
      odoUnif 1 (2 * M) (T - 1) (fun _ => (2 : ℤ))) : False := by
  have hr := odoUnif_dim_one_succ_at_one M (T - 1) (by omega)
  rw [show T - 1 + 1 = T by omega] at hr
  have hd1 := odoUnif_dim_one_two_le_one M (T - 1) hM
  have hd2 := odoUnif_dim_one_one_le_two_add_one M (T - 1) hM
  have hd3 := odoUnif_dim_one_two_le_one M T hM
  have hb1 := odoUnif_le_succ_le_add_one 1 (2 * M) (T - 1) (fun _ => (2 : ℤ))
  rw [show T - 1 + 1 = T by omega] at hb1
  have hb2 := odoUnif_le_succ_le_add_one 1 (2 * M) T (fun _ => (2 : ℤ))
  have haT : odoUnif 1 (2 * M) T (fun _ => (1 : ℤ)) =
      odoUnif 1 (2 * M) T (fun _ => (2 : ℤ)) := by
    split_ifs at hr <;> omega
  have e21 : (fun i : Fin 1 => (fun _ : Fin 1 => (2 : ℤ)) i - 1) = fun _ => (1 : ℤ) := by
    funext i; norm_num
  have h1 : odoUnif 1 (2 * M) (T + 1) (fun _ => (2 : ℤ)) =
      odoUnif 1 (2 * (M - 1)) (T + 1) (fun _ => (1 : ℤ)) := by
    rw [← e21]
    refine selfsim_shift_succ_of_reflect hM hC (fun _ => (2 : ℤ)) (fun _ => le_refl _) (fun k _ => ?_)
    rw [Fin.eq_zero k, constSite_one_sub_unit]
    norm_num
    exact haT
  have h2 : odoUnif 1 (2 * M) (T - 1) (fun _ => (2 : ℤ)) =
      odoUnif 1 (2 * (M - 1)) (T - 1) (fun _ => (1 : ℤ)) := by
    rw [← e21]
    exact hC' (fun _ => (2 : ℤ)) (fun _ => le_refl _)
  have hz : inSimplex 1 (M - 1) (fun _ => (1 : ℤ)) := by
    refine ⟨fun _ => ⟨le_refl _, ?_⟩, fun _ _ _ => le_refl _⟩
    show (1 : ℤ) ≤ ((M - 1 : ℕ) : ℤ)
    exact_mod_cast (by omega : 1 ≤ M - 1)
  have h3 := hW _ hz
  rw [h1, h2] at hbad
  omega

/-- The point `1` cannot rise by two between `T` and `T + 2`. -/
theorem topple_one_dim_x1 (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (T + 2) (fun _ => (1 : ℤ)) -
      odoUnif 1 (2 * M) T (fun _ => (1 : ℤ))) : False := by
  refine topple_one_dim_y2 hM hT hC hC' hW ?_
  have hr0 := odoUnif_dim_one_succ_at_one M T (by omega)
  have hr1 := odoUnif_dim_one_succ_at_one M (T + 1) (by omega)
  have hrm := odoUnif_dim_one_succ_at_one M (T - 1) (by omega)
  rw [show T - 1 + 1 = T by omega] at hrm
  have hd0 := odoUnif_dim_one_two_le_one M T hM
  have hd1 := odoUnif_dim_one_two_le_one M (T + 1) hM
  have hdm := odoUnif_dim_one_two_le_one M (T - 1) hM
  have hb0 := odoUnif_le_succ_le_add_one 1 (2 * M) T (fun _ => (2 : ℤ))
  have hbm := odoUnif_le_succ_le_add_one 1 (2 * M) (T - 1) (fun _ => (2 : ℤ))
  rw [show T - 1 + 1 = T by omega] at hbm
  have ham := odoUnif_le_succ_le_add_one 1 (2 * M) (T - 1) (fun _ => (1 : ℤ))
  rw [show T - 1 + 1 = T by omega] at ham
  rw [show T + 1 + 1 = T + 2 by omega] at hr1
  split_ifs at hr0 hr1 hrm <;> omega

/-- The point `2` cannot rise by two between `T` and `T + 2`. -/
theorem topple_one_dim_x2 (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (T + 2) (fun _ => (2 : ℤ)) -
      odoUnif 1 (2 * M) T (fun _ => (2 : ℤ))) : False := by
  rcases odoUnif_dim_one_rise_two_nbr M T hT 2 hbad with h3 | h1
  · exact topple_one_dim_y3 hM hC hC' hW 3 (le_refl _) (by norm_num at h3; exact h3)
  · norm_num at h1
    refine topple_one_dim_y2 hM hT hC hC' hW ?_
    have hr0 := odoUnif_dim_one_succ_at_one M T (by omega)
    have hrm := odoUnif_dim_one_succ_at_one M (T - 1) (by omega)
    rw [show T - 1 + 1 = T by omega] at hrm
    have hd0 := odoUnif_dim_one_two_le_one M T hM
    have hdm := odoUnif_dim_one_two_le_one M (T - 1) hM
    have hb0 := odoUnif_le_succ_le_add_one 1 (2 * M) T (fun _ => (2 : ℤ))
    have hb1 := odoUnif_le_succ_le_add_one 1 (2 * M) (T + 1) (fun _ => (2 : ℤ))
    rw [show T + 1 + 1 = T + 2 by omega] at hb1
    have hbm := odoUnif_le_succ_le_add_one 1 (2 * M) (T - 1) (fun _ => (2 : ℤ))
    rw [show T - 1 + 1 = T by omega] at hbm
    split_ifs at hr0 hrm <;> omega

/-- A point `c ≥ 3` cannot rise by two between `T` and `T + 2`. -/
theorem topple_one_dim_x3 (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1)
    (c : ℤ) (hc : 3 ≤ c)
    (hbad : 2 ≤ odoUnif 1 (2 * M) (T + 2) (fun _ => c) -
      odoUnif 1 (2 * M) T (fun _ => c)) : False := by
  rcases odoUnif_dim_one_rise_two_nbr M T hT c hbad with hp | hm
  · exact topple_one_dim_y3 hM hC hC' hW (c + 1) (by omega) hp
  · by_cases hc3 : c = 3
    · subst hc3
      norm_num at hm
      exact topple_one_dim_y2 hM hT hC hC' hW hm
    · exact topple_one_dim_y3 hM hC hC' hW (c - 1) (by omega) hm

/-- Strong topple control in one dimension at the topple time `T`. -/
theorem topple_one_dim_at (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hC : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) T y = odoUnif 1 (2 * (M - 1)) T (fun i => y i - 1))
    (hC' : ∀ y : Site 1, (∀ i, 2 ≤ y i) →
      odoUnif 1 (2 * M) (T - 1) y = odoUnif 1 (2 * (M - 1)) (T - 1) (fun i => y i - 1))
    (hW : ∀ z : Site 1, inSimplex 1 (M - 1) z →
      odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z ≤ 1) :
    simplexMax 1 M (fun z => odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z) ≤ 1 := by
  refine simplexMax_le 1 M _ 1 (by norm_num) (fun z hz => ?_)
  by_contra hcon
  have hbad : 2 ≤ odoUnif 1 (2 * M) (T + 2) z - odoUnif 1 (2 * M) T z := by omega
  rw [site_one_eq_const z] at hbad
  have h1 := (hz.1 0).1
  rcases (show z 0 = 1 ∨ z 0 = 2 ∨ 3 ≤ z 0 by omega) with h | h | h
  · rw [h] at hbad
    exact topple_one_dim_x1 hM hT hC hC' hW hbad
  · rw [h] at hbad
    exact topple_one_dim_x2 hM hT hC hC' hW hbad
  · exact topple_one_dim_x3 hM hT hC hC' hW (z 0) h hbad

end OneDimAt

/-! ### Dimensions at least two -/

/-- The parabolic least action principle of `dimred.tex:1455-1458`: the odometer
on the slice `x_{d} = 1` is dominated by the odometer one dimension lower. -/
theorem odoUnif_snoc_one_le (e N s : ℕ) (he : 1 ≤ e) (x : Site e) :
    odoUnif (e + 1) N s (Fin.snoc x 1) ≤ odoUnif e N s x := by
  classical
  let u : ℕ → Site (e + 1) → ℤ := fun t y =>
    if inCube (e + 1) N y then odoUnif e N t (Fin.init y) else 0
  have hvnn : ∀ t (z : Site e), 0 ≤ odoUnif e N t z := fun t z => odo_nonneg _ _ _ _ _
  have hu0 : ∀ t y, 0 ≤ u t y := by
    intro t y
    simp only [u]
    split_ifs
    · exact hvnn _ _
    · exact le_refl _
  have hu1 : ∀ t y, ¬ inCube (e + 1) N y → u t y = 0 := by
    intro t y hy
    simp only [u, if_neg hy]
  have hu_snoc : ∀ t (z : Site e) (c : ℤ), loCoord N ≤ c → c ≤ hiCoord N →
      u t (Fin.snoc z c) = odoUnif e N t z := by
    intro t z c h0 h1
    simp only [u]
    by_cases hz : inCube e N z
    · rw [if_pos ((inCube_snoc z c).mpr ⟨hz, h0, h1⟩), Fin.init_snoc]
    · rw [if_neg (fun h => hz ((inCube_snoc z c).mp h).1)]
      exact (odo_eq_zero_outside _ _ _ _ _ hz).symm
  have hu_le : ∀ t (z : Site e) (c : ℤ), u t (Fin.snoc z c) ≤ odoUnif e N t z := by
    intro t z c
    simp only [u]
    split_ifs
    · rw [Fin.init_snoc]
    · exact hvnn _ _
  have hpc_e := (Frozen.parabolic_comparison e N he (fun _ => 2 * (e : ℤ))
    (fun _ _ => by linarith)).1
  have hsup : ∀ (t : ℕ) (y : Site (e + 1)), inCube (e + 1) N y →
      (-(2 * ((e + 1 : ℕ) : ℤ)) * u (t + 1) y + nbrSum (u t) y) +
        2 * ((e + 1 : ℕ) : ℤ) ≤ 2 * ((e + 1 : ℕ) : ℤ) - 1 := by
    intro t y hy
    obtain ⟨y', c, rfl⟩ : ∃ (y' : Site e) (c : ℤ), y = Fin.snoc y' c :=
      ⟨Fin.init y, y (Fin.last e), (Fin.snoc_init_self y).symm⟩
    obtain ⟨hy', hc0, hc1⟩ := (inCube_snoc y' c).mp hy
    have hcast : ∀ i : Fin e,
        u t (Fin.snoc y' c + unit (Fin.castSucc i)) + u t (Fin.snoc y' c - unit (Fin.castSucc i))
          = odoUnif e N t (y' + unit i) + odoUnif e N t (y' - unit i) := by
      intro i
      rw [← snoc_add_unit, ← snoc_sub_unit, hu_snoc t _ c hc0 hc1, hu_snoc t _ c hc0 hc1]
    have hl1 := hu_le t y' (c + 1)
    have hl2 := hu_le t y' (c - 1)
    rw [snoc_add_unit_last] at hl1
    rw [snoc_sub_unit_last] at hl2
    rw [nbrSum_snoc, Finset.sum_congr rfl (fun i _ => hcast i), hu_snoc (t + 1) y' c hc0 hc1]
    have h1 : (-(2 * (e : ℤ)) * odoUnif e N (t + 1) y' +
        ∑ i : Fin e, (odoUnif e N t (y' + unit i) + odoUnif e N t (y' - unit i))) +
          2 * (e : ℤ) ≤ 2 * (e : ℤ) - 1 := hpc_e t y' hy'
    have hm : odoUnif e N t y' ≤ odoUnif e N (t + 1) y' :=
      odo_mono _ _ _ (Nat.le_succ t) y'
    push_cast
    nlinarith
  have hpc := (Frozen.parabolic_comparison (e + 1) N (by omega)
    (fun _ => 2 * ((e + 1 : ℕ) : ℤ))
    (fun _ _ => by push_cast; linarith)).2 u hu0 hu1 hsup s (Fin.snoc x 1)
  exact le_trans hpc (hu_le s x 1)

/-- The reflecting boundary identity `eq:reflecting_boundaries` at one time, from
self-similarity in dimensions `e + 1` and `e` and dimensional reduction at the
scales `M` and `M - 1`, `dimred.tex:1171-1180`. -/
theorem odoUnif_snoc_two_eq_snoc_one {e M T : ℕ}
    (hCd : ∀ y : Site (e + 1), (∀ i, 2 ≤ y i) →
      odoUnif (e + 1) (2 * M) T y = odoUnif (e + 1) (2 * (M - 1)) T (fun i => y i - 1))
    (hCe : ∀ y : Site e, (∀ i, 2 ≤ y i) →
      odoUnif e (2 * M) T y = odoUnif e (2 * (M - 1)) T (fun i => y i - 1))
    (hredM : ∀ z : Site e, odoUnif (e + 1) (2 * M) T (Fin.snoc z 1) = odoUnif e (2 * M) T z)
    (hredM1 : ∀ z : Site e,
      odoUnif (e + 1) (2 * (M - 1)) T (Fin.snoc z 1) = odoUnif e (2 * (M - 1)) T z)
    (z : Site e) (hz : ∀ i, 2 ≤ z i) :
    odoUnif (e + 1) (2 * M) T (Fin.snoc z 2) = odoUnif (e + 1) (2 * M) T (Fin.snoc z 1) := by
  have hs : (fun i => (Fin.snoc z 2 : Site (e + 1)) i - 1) = Fin.snoc (fun i => z i - 1) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  have h2 : ∀ i, 2 ≤ (Fin.snoc z 2 : Site (e + 1)) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hz j
  rw [hCd _ h2, hs, hredM1, ← hCe z hz, ← hredM]

/-- The reflecting boundary identity at an unsorted point, by the coordinate
permutation moving the coordinate equal to two to the last place. -/
theorem odoUnif_sub_unit_eq_of_eq_two {e M T : ℕ}
    (hsnoc : ∀ z : Site e, (∀ i, 2 ≤ z i) →
      odoUnif (e + 1) (2 * M) T (Fin.snoc z 2) = odoUnif (e + 1) (2 * M) T (Fin.snoc z 1))
    (y : Site (e + 1)) (hy : ∀ i, 2 ≤ y i) (k : Fin (e + 1)) (hk : y k = 2) :
    odoUnif (e + 1) (2 * M) T (y - unit k) = odoUnif (e + 1) (2 * M) T y := by
  let σ : Equiv.Perm (Fin (e + 1)) := Equiv.swap k (Fin.last e)
  have hsym : ∀ x : Site (e + 1),
      odoUnif (e + 1) (2 * M) T (fun i => x (σ i)) = odoUnif (e + 1) (2 * M) T x := by
    intro x
    have h := odo_cubeSym (e + 1) (2 * M) (fun _ => 2 * ((e + 1 : ℕ) : ℤ))
      (isSymmetricPile_const' (e + 1) (2 * M) _) T σ (fun _ => true) x
    have hc : cubeSym (e + 1) (2 * M) σ (fun _ => true) x = fun i => x (σ i) := by
      funext i
      simp [cubeSym]
    rw [hc] at h
    exact h
  let z : Site e := fun i => y (σ (Fin.castSucc i))
  have hz2 : ∀ i, 2 ≤ z i := fun i => hy _
  have hne : ∀ j : Fin e, σ (Fin.castSucc j) ≠ k := by
    intro j h
    have h' : Fin.castSucc j = σ k := by
      rw [← h]
      simp [σ]
    simp only [σ, Equiv.swap_apply_left] at h'
    exact (Fin.castSucc_lt_last j).ne h'
  have e1 : (fun i => y (σ i)) = Fin.snoc z 2 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [σ, hk]
    · simp [z]
  have e2 : (fun i => (y - unit k) (σ i)) = Fin.snoc z 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [σ, Equiv.swap_apply_right, Fin.snoc_last]
      rw [sub_unit_self, hk]
      norm_num
    · rw [Fin.snoc_castSucc, sub_unit_other _ _ _ _ (hne j)]
  rw [← hsym (y - unit k), ← hsym y, e1, e2]
  exact (hsnoc z hz2).symm

/-- The paper's Case 3, `dimred.tex:1473-1474`: a point with every coordinate at
least three is two steps inside the self-similar region, so its two-step rise
is the rise at scale `M - 1`. -/
theorem topple_rise_le_one_of_three_le {d M T : ℕ} (hM : 2 ≤ M)
    (hC : ∀ y : Site d, (∀ i, 2 ≤ y i) →
      odoUnif d (2 * M) T y = odoUnif d (2 * (M - 1)) T (fun i => y i - 1))
    (hrefl : ∀ y : Site d, (∀ i, 2 ≤ y i) → ∀ k, y k = 2 →
      odoUnif d (2 * M) T (y - unit k) = odoUnif d (2 * M) T y)
    (hW : simplexMax d (M - 1) (fun z =>
      odoUnif d (2 * (M - 1)) (T + 2) z - odoUnif d (2 * (M - 1)) T z) ≤ 1)
    (x : Site d) (hx : inSimplex d M x) (hx3 : ∀ i, 3 ≤ x i) :
    odoUnif d (2 * M) (T + 2) x - odoUnif d (2 * M) T x ≤ 1 := by
  have hC1 : ∀ y : Site d, (∀ i, 2 ≤ y i) →
      odoUnif d (2 * M) (T + 1) y = odoUnif d (2 * (M - 1)) (T + 1) (fun i => y i - 1) :=
    fun y hy => selfsim_shift_succ_of_reflect hM hC y hy (hrefl y hy)
  have hC2 : odoUnif d (2 * M) (T + 1 + 1) x =
      odoUnif d (2 * (M - 1)) (T + 1 + 1) (fun i => x i - 1) :=
    selfsim_shift_succ_of_reflect hM hC1 x (fun i => by have := hx3 i; omega)
      (fun k hk => absurd hk (by have := hx3 k; omega))
  have hsh : inSimplex d (M - 1) (fun i => x i - 1) := by
    refine ⟨fun i => ⟨show (1 : ℤ) ≤ x i - 1 by have := hx3 i; omega, ?_⟩,
      fun i j hij => ?_⟩
    · have := (hx.1 i).2
      show x i - 1 ≤ ((M - 1 : ℕ) : ℤ)
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      push_cast
      omega
    · have := hx.2 i j hij
      show x j - 1 ≤ x i - 1
      omega
  have hle := le_simplexMax d (M - 1) (fun z =>
    odoUnif d (2 * (M - 1)) (T + 2) z - odoUnif d (2 * (M - 1)) T z) _ hsh
  rw [hC x (fun i => by have := hx3 i; omega)]
  change odoUnif d (2 * M) (T + 1 + 1) x - _ ≤ 1
  rw [hC2]
  exact le_trans hle hW

/-- Strong topple control at the topple time in dimension `e + 1 ≥ 2`,
`dimred.tex:1447-1474`. -/
theorem topple_dim_succ_at {e M T : ℕ} (he : 1 ≤ e) (hM : 2 ≤ M)
    (hC : ∀ y : Site (e + 1), (∀ i, 2 ≤ y i) →
      odoUnif (e + 1) (2 * M) T y = odoUnif (e + 1) (2 * (M - 1)) T (fun i => y i - 1))
    (hsnoc : ∀ z : Site e, (∀ i, 2 ≤ z i) →
      odoUnif (e + 1) (2 * M) T (Fin.snoc z 2) = odoUnif (e + 1) (2 * M) T (Fin.snoc z 1))
    (hred : ∀ x : Site e, inSimplex e M x →
      odoUnif (e + 1) (2 * M) T (Fin.snoc x 1) = odoUnif e (2 * M) T x)
    (hlow : simplexMax e M (fun x =>
      odoUnif e (2 * M) (T + 2) x - odoUnif e (2 * M) T x) ≤ 1)
    (hW : 3 ≤ M → simplexMax (e + 1) (M - 1) (fun z =>
      odoUnif (e + 1) (2 * (M - 1)) (T + 2) z - odoUnif (e + 1) (2 * (M - 1)) T z) ≤ 1) :
    simplexMax (e + 1) M (fun x =>
      odoUnif (e + 1) (2 * M) (T + 2) x - odoUnif (e + 1) (2 * M) T x) ≤ 1 := by
  have hcase1 : ∀ y : Site e, inSimplex e M y →
      2 ≤ odoUnif (e + 1) (2 * M) (T + 2) (Fin.snoc y 1) -
        odoUnif (e + 1) (2 * M) T (Fin.snoc y 1) → False := by
    intro y hy hbad
    have h1 := odoUnif_snoc_one_le e (2 * M) (T + 2) he y
    have h2 := hred y hy
    have h3 := le_simplexMax e M (fun x =>
      odoUnif e (2 * M) (T + 2) x - odoUnif e (2 * M) T x) y hy
    linarith
  refine simplexMax_le (e + 1) M _ 1 (by norm_num) (fun x hx => ?_)
  by_contra hcon
  have hbad : 2 ≤ odoUnif (e + 1) (2 * M) (T + 2) x - odoUnif (e + 1) (2 * M) T x := by
    omega
  obtain ⟨y, c, rfl⟩ : ∃ (y : Site e) (c : ℤ), x = Fin.snoc y c :=
    ⟨Fin.init x, x (Fin.last e), (Fin.snoc_init_self x).symm⟩
  obtain ⟨hy, hc1, hcM, hcy⟩ := (inSimplex_snoc y c).mp hx
  rcases (show c = 1 ∨ c = 2 ∨ 3 ≤ c by omega) with h | h | h
  · subst h
    exact hcase1 y hy hbad
  · subst h
    apply hcase1 y hy
    have hy1 : inSimplex (e + 1) M (Fin.snoc y 1) := (inSimplex_snoc_one (by omega) y).mpr hy
    have he2 : Fin.snoc y 1 + unit (Fin.last e) - ∑ j ∈ (∅ : Finset (Fin (e + 1))), unit j =
        (Fin.snoc y 2 : Site (e + 1)) := by
      rw [Finset.sum_empty, sub_zero, ← snoc_add_unit_last]
      norm_num
    have hmem : inSimplex (e + 1) M
        (Fin.snoc y 1 + unit (Fin.last e) - ∑ j ∈ (∅ : Finset (Fin (e + 1))), unit j) := by
      rw [he2]; exact hx
    have hax := Frozen.axis_monotonicity (e + 1) M (by omega) (2 * ((e + 1 : ℕ) : ℤ))
        (T + 2) (by omega) (Fin.snoc y 1) hy1
      (Fin.last e) ∅ (by simp) (by simp) hmem
    rw [he2] at hax
    have hr := hsnoc y hcy
    change odoUnif (e + 1) (2 * M) (T + 2) (Fin.snoc y 2) ≤
      odoUnif (e + 1) (2 * M) (T + 2) (Fin.snoc y 1) at hax
    linarith
  · have hx3 : ∀ i, 3 ≤ (Fin.snoc y c : Site (e + 1)) i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using h
      · simp only [Fin.snoc_castSucc]
        have := hcy j
        omega
    have hle := topple_rise_le_one_of_three_le hM hC
      (fun y' hy' k hk => odoUnif_sub_unit_eq_of_eq_two hsnoc y' hy' k hk)
      (hW (by have : c ≤ (M : ℤ) := hcM; omega)) _ hx hx3
    omega

/-! ### Scale one and the topple times -/

theorem eq_one_of_inSimplex_one {d : ℕ} (z : Site d) (hz : inSimplex d 1 z) :
    z = fun _ => (1 : ℤ) := by
  funext i
  have h := hz.1 i
  have h2 : z i ≤ 1 := by exact_mod_cast h.2
  exact le_antisymm h2 h.1

/-- At scale one every site topples once and then never again. -/
theorem odoUnif_scale_one_sub_le_one (d a b : ℕ) (hd : 1 ≤ d) (z : Site d) (hz : inSimplex d 1 z) :
    odoUnif d (2 * 1) a z - odoUnif d (2 * 1) b z ≤ 1 := by
  rw [eq_one_of_inSimplex_one z hz]
  change odoUnif d 2 a _ - odoUnif d 2 b _ ≤ 1
  rw [odoUnif_one_scale d a hd, odoUnif_one_scale d b hd]
  split_ifs <;> norm_num

/-- Dimensional reduction at scale one. -/
theorem odoUnif_scale_one_snoc_one (e s : ℕ) (he : 1 ≤ e) (z : Site e) :
    odoUnif (e + 1) (2 * 1) s (Fin.snoc z 1) = odoUnif e (2 * 1) s z := by
  refine odoUnif_snoc_of_reduction e 1 s (fun w hw => ?_) z
  rw [eq_one_of_inSimplex_one w hw]
  have hs : (Fin.snoc (fun _ : Fin e => (1 : ℤ)) 1 : Site (e + 1)) = fun _ => (1 : ℤ) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hs]
  change odoUnif (e + 1) 2 s _ = odoUnif e 2 s _
  rw [odoUnif_one_scale (e + 1) s (by omega), odoUnif_one_scale e s he]

/-- The topple time is monotone in the scale in one dimension, from the
self-similarity clause at the smaller scale. -/
theorem toppleTime_one_scale_mono_of_regConsist (M : ℕ) (hM : 3 ≤ M) (hcons : ∀ n, RegConsist 1 (M - 1) n) :
    toppleTime 1 (M - 2) ≤ toppleTime 1 (M - 1) := by
  have hc1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  have hc2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ M)]; norm_num
  refine toppleTime_mono_scale (M - 2) (M - 1) (by omega) (by omega) (fun n hn => ?_)
    (corner_reaches 1 (M - 1) (le_refl 1) (by omega) (fun _ he hed => absurd hed (by omega)))
    (corner_reaches 1 (M - 2) (le_refl 1) (by omega) (fun _ he hed => absurd hed (by omega)))
  have h := hcons n (M - 2) (by omega) (by omega) hn (cornerPoint 1 (M - 1))
    (cornerPoint_mem_inSimplex 1 (M - 1) (by omega)) (fun i => by
      rw [cornerPoint_one]; dsimp only; omega)
  rw [h, cornerPoint_one, cornerPoint_one]
  congr 1
  funext i
  rw [hc1, hc2]
  ring

/-- The topple time does not depend on the dimension, given dimensional reduction
at that scale in every lower dimension. -/
theorem toppleTime_eq_toppleTime_one (j D : ℕ) (hj : 1 ≤ j)
    (hred : ∀ e : ℕ, 1 ≤ e → e < D → ∀ (t : ℕ) (y : Site e), inSimplex e j y →
      odoUnif (e + 1) (2 * j) t (Fin.snoc y 1) = odoUnif e (2 * j) t y) :
    ∀ d, 1 ≤ d → d ≤ D → toppleTime d j = toppleTime 1 j := by
  intro d hd hdD
  induction d, hd using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih (by omega)]
    exact le_antisymm
      (toppleTime_mono_dim_le n j hn hj (hred n hn (by omega))
        (fun e he hed => hred e he (by omega)))
      (toppleTime_mono_dim n j hn hj (hred n hn (by omega))
        (fun e he hed => hred e he (by omega)))

/-! ### The induction step -/

/-- Strong topple control at one triple of the joint induction,
`dimred.tex:944-948`, proved from the earlier triples and the self-similarity
and dimensional-reduction clauses at the current triple. -/
theorem topple_step_of_earlier (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hdimred : DimRedAt d M t) (hfacet : RegStrongFacet d M t)
    (hconsist : RegConsist d M t) :
    RegTopple d M t := by
  intro ht
  obtain ⟨T, hT, hTt⟩ := (WithTop.le_coe_iff).mp ht
  replace hT : toppleTime d (M - 1) = (T : ℕ∞) := hT
  have hTpos : 1 ≤ T := by
    have htop := one_le_toppleTime d (M - 1)
    rw [hT] at htop
    exact ENat.coe_le_coe.mp htop
  have hconsAt : ∀ s, s ≤ t → RegConsist d M s := by
    intro s hs
    rcases Nat.lt_or_ge s t with h | h
    · exact (hprior d M s (Or.inr (Or.inr ⟨rfl, rfl, h⟩)) hd hM).1.1
    · rw [show s = t by omega]; exact hconsist
  have hdimAt : ∀ s, s ≤ t → DimRedAt d M s := by
    intro s hs
    rcases Nat.lt_or_ge s t with h | h
    · exact (hprior d M s (Or.inr (Or.inr ⟨rfl, rfl, h⟩)) hd hM).2
    · rw [show s = t by omega]; exact hdimred
  have hCs : ∀ s, s ≤ T → ∀ y : Site d, (∀ i, 2 ≤ y i) →
      odoUnif d (2 * M) s y = odoUnif d (2 * (M - 1)) s (fun i => y i - 1) := by
    intro s hs
    exact selfsim_shift_of_simplex hM (selfsim_shift_simplex_of_regConsist hM (hconsAt s (le_trans hs hTt))
      (by rw [hT]; exact ENat.coe_le_coe.mpr hs))
  have hbase : simplexMax d M (fun x =>
      odoUnif d (2 * M) (T + 2) x - odoUnif d (2 * M) T x) ≤ 1 := by
    rcases (show d = 1 ∨ 2 ≤ d by omega) with hd1 | hd2
    · subst hd1
      refine topple_one_dim_at hM hTpos (hCs T le_rfl) (hCs (T - 1) (by omega)) ?_
      intro z hz
      rcases (show M = 2 ∨ 3 ≤ M by omega) with hM2 | hM3
      · subst hM2
        exact odoUnif_scale_one_sub_le_one 1 (T + 1) (T - 1) le_rfl z hz
      · have hmono := toppleTime_one_scale_mono_of_regConsist M hM3 (fun n =>
          (hprior 1 (M - 1) n (Or.inr (Or.inl ⟨rfl, by omega⟩)) le_rfl (by omega)).1.1)
        have hc1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
        have hc2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ M)]; norm_num
        have hxM : inSimplex 1 M (fun _ => (M : ℤ)) :=
          ⟨fun _ => ⟨show (1 : ℤ) ≤ (M : ℤ) by exact_mod_cast (by omega : 1 ≤ M), le_refl _⟩,
            fun _ _ _ => le_refl _⟩
        have hgap := one_dim_tau_gap M t hM3 ht hconsist (fun q' hq' => by
          have hq'T : (q' : ℕ∞) ≤ (T : ℕ∞) := by rw [← hT]; exact le_trans hq' hmono
          have hC := hconsAt q' (le_trans (ENat.coe_le_coe.mp hq'T) hTt)
          constructor
          · have h := hC (M - 1) (by omega) (by omega) (le_trans hq' hmono)
              (fun _ => (M : ℤ)) hxM (fun _ => by rw [hc1]; omega)
            rw [h]
            congr 1
            funext _
            rw [hc1]
            ring
          · have h := hC (M - 2) (by omega) (by omega) hq'
              (fun _ => (M : ℤ)) hxM (fun _ => by rw [hc2]; omega)
            rw [h]
            congr 1
            funext _
            rw [hc2]
            ring) hprior
        rw [hT] at hgap
        have hfin : toppleTime 1 (M - 2) ≠ ⊤ := by
          intro h
          rw [h, top_add] at hgap
          exact ENat.coe_ne_top T (top_le_iff.mp hgap)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
        replace hn : (n : ℕ∞) = toppleTime 1 (M - 2) := hn
        rw [← hn] at hgap
        have hnT : n + 2 ≤ T := by
          have h2 : ((n + 2 : ℕ) : ℕ∞) ≤ (T : ℕ∞) := by push_cast; exact hgap
          exact ENat.coe_le_coe.mp h2
        have hlow : toppleTime 1 (M - 1 - 1) ≤ ((T - 1 : ℕ) : ℕ∞) := by
          rw [show M - 1 - 1 = M - 2 by omega, ← hn]
          exact ENat.coe_le_coe.mpr (by omega)
        have htop := (hprior 1 (M - 1) (T - 1) (Or.inr (Or.inl ⟨rfl, by omega⟩)) le_rfl
          (by omega)).1.2.2.2.2 hlow
        rw [show T - 1 + 2 = T + 1 by omega] at htop
        exact le_trans (le_simplexMax 1 (M - 1) (fun z =>
          odoUnif 1 (2 * (M - 1)) (T + 1) z - odoUnif 1 (2 * (M - 1)) (T - 1) z) z hz) htop
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have he : 1 ≤ e := by omega
      have hDR : ∀ j, 2 ≤ j → j < M → ∀ e', 1 ≤ e' → e' < e + 1 → ∀ (t' : ℕ) (y : Site e'),
          inSimplex e' j y →
          odoUnif (e' + 1) (2 * j) t' (Fin.snoc y 1) = odoUnif e' (2 * j) t' y := by
        intro j hj2 hjM e' he' hed t' y hy
        have hre : regEarlier (e + 1) M t (e' + 1) j t' := by
          rcases Nat.lt_or_ge (e' + 1) (e + 1) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨by omega, hjM⟩)
        exact (hprior (e' + 1) j t' hre (by omega) hj2).2 e' he' rfl y hy
      have htauEq : ∀ j, 1 ≤ j → j < M → ∀ D, 1 ≤ D → D ≤ e + 1 →
          toppleTime D j = toppleTime 1 j := by
        intro j hj hjM
        rcases (show j = 1 ∨ 2 ≤ j by omega) with h1 | h2
        · subst h1
          intro D hD _
          rw [toppleTime_one_eq_one D hD, toppleTime_one_eq_one 1 le_rfl]
        · exact toppleTime_eq_toppleTime_one j (e + 1) hj (hDR j h2 hjM)
      have hTe : toppleTime e (M - 1) = (T : ℕ∞) := by
        rw [htauEq (M - 1) (by omega) (by omega) e he (by omega),
          ← htauEq (M - 1) (by omega) (by omega) (e + 1) (by omega) le_rfl, hT]
      have hCe : ∀ y : Site e, (∀ i, 2 ≤ y i) →
          odoUnif e (2 * M) T y = odoUnif e (2 * (M - 1)) T (fun i => y i - 1) :=
        selfsim_shift_of_simplex hM (selfsim_shift_simplex_of_regConsist hM
          (hprior e M T (Or.inl (by omega)) he hM).1.1 (by rw [hTe]))
      have hred : ∀ x : Site e, inSimplex e M x →
          odoUnif (e + 1) (2 * M) T (Fin.snoc x 1) = odoUnif e (2 * M) T x :=
        fun x hx => hdimAt T hTt e he rfl x hx
      have hredM1 : ∀ z : Site e,
          odoUnif (e + 1) (2 * (M - 1)) T (Fin.snoc z 1) = odoUnif e (2 * (M - 1)) T z := by
        rcases (show M = 2 ∨ 3 ≤ M by omega) with hM2 | hM3
        · subst hM2
          exact odoUnif_scale_one_snoc_one e T he
        · exact odoUnif_snoc_of_reduction e (M - 1) T
            (fun x hx => hDR (M - 1) (by omega) (by omega) e he (by omega) T x hx)
      have hsnoc := odoUnif_snoc_two_eq_snoc_one (hCs T le_rfl) hCe (odoUnif_snoc_of_reduction e M T hred)
        hredM1
      have hlow : simplexMax e M (fun x =>
          odoUnif e (2 * M) (T + 2) x - odoUnif e (2 * M) T x) ≤ 1 :=
        (hprior e M T (Or.inl (by omega)) he hM).1.2.2.2.2 (by rw [hTe])
      have hW : 3 ≤ M → simplexMax (e + 1) (M - 1) (fun z =>
          odoUnif (e + 1) (2 * (M - 1)) (T + 2) z - odoUnif (e + 1) (2 * (M - 1)) T z) ≤ 1 := by
        intro hM3
        have hmono := toppleTime_one_scale_mono_of_regConsist M hM3 (fun n =>
          (hprior 1 (M - 1) n (Or.inl (by omega)) le_rfl (by omega)).1.1)
        have hle : toppleTime (e + 1) (M - 1 - 1) ≤ (T : ℕ∞) := by
          rw [show M - 1 - 1 = M - 2 by omega,
            htauEq (M - 2) (by omega) (by omega) (e + 1) (by omega) le_rfl, ← hT,
            htauEq (M - 1) (by omega) (by omega) (e + 1) (by omega) le_rfl]
          exact hmono
        exact (hprior (e + 1) (M - 1) T (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega)
          (by omega)).1.2.2.2.2 hle
      exact topple_dim_succ_at he hM (hCs T le_rfl) hsnoc hred hlow hW
  have hlim := Frozen.topple_limit d M hd (by omega) (fun _ => 2 * (d : ℤ))
    (fun _ _ _ _ => rfl) T t 2 hTt
  simp only [Corrected.maximum_eq_simplexMax] at hlim
  exact le_trans hlim hbase

end DimRed
