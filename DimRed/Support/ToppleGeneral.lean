/-
Strong topple control in dimensions at least two, the clause
`base_dimension:strong_topple` of `dimred.tex:944-948`, with the three-case
argument at `dimred.tex:1447-1473`.  Dimensional reduction, the reflecting
boundary comparison, axis monotonicity, least-action comparison, and the
lower-dimensional control are explicit inputs.  The remaining neighbour
transfer is isolated as the local induction input for the third case.
-/
import DimRed.Support.SnocSimplex
import DimRed.Support.ToppleTime
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

theorem topple_general (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime (d + 1) (M - 1) ≤ (t : ℕ∞))
    (hred : ∀ (T : ℕ), toppleTime (d + 1) (M - 1) = (T : ℕ∞) →
      ∀ x : Site d, inSimplex d M x →
        odoUnif (d + 1) (2 * M) T (Fin.snoc x 1) = odoUnif d (2 * M) T x)
    (hreflect : ∀ (T : ℕ), toppleTime (d + 1) (M - 1) = (T : ℕ∞) →
      ∀ x : Site d, inSimplex d M x →
        odoUnif (d + 1) (2 * M) T (Fin.snoc x 1) =
          odoUnif (d + 1) (2 * M) T (Fin.snoc x 1 + unit (Fin.last d)))
    (haxis : ∀ (s : ℕ), 1 ≤ s → ∀ x : Site (d + 1), inSimplex (d + 1) M x →
      ∀ i : Fin (d + 1), ∀ J : Finset (Fin (d + 1)), J.card ≤ 1 →
        (∀ j ∈ J, i < j) →
        inSimplex (d + 1) M (x + unit i - ∑ j ∈ J, unit j) →
        odoUnif (d + 1) (2 * M) s (x + unit i - ∑ j ∈ J, unit j) ≤
          odoUnif (d + 1) (2 * M) s x)
    (hleast : ∀ (T : ℕ), toppleTime (d + 1) (M - 1) = (T : ℕ∞) →
      ∀ x : Site d, inSimplex d M x →
        odoUnif (d + 1) (2 * M) (T + 2) (Fin.snoc x 1) ≤
          odoUnif d (2 * M) (T + 2) x)
    (hlower : ∀ (s : ℕ), toppleTime d (M - 1) ≤ (s : ℕ∞) →
      simplexMax d M (fun x =>
        odoUnif d (2 * M) (s + 2) x - odoUnif d (2 * M) s x) ≤ 1)
    (hlower_time : ∀ (T : ℕ), toppleTime (d + 1) (M - 1) = (T : ℕ∞) →
      toppleTime d (M - 1) ≤ (T : ℕ∞) ∧
        toppleTime d (M - 1) ≤ ((T - 1 : ℕ) : ℕ∞))
    (hneighbor : ∀ (T : ℕ), toppleTime (d + 1) (M - 1) = (T : ℕ∞) →
      ∀ x : Site (d + 1), inSimplex (d + 1) M x → 3 ≤ x (Fin.last d) →
      2 ≤ odoUnif (d + 1) (2 * M) (T + 2) x -
        odoUnif (d + 1) (2 * M) T x →
      ∃ y : Site (d + 1), ∃ z : Site d, ∃ i : Fin (d + 1),
        inSimplex (d + 1) M y ∧ inSimplex d M z ∧ 2 ≤ y (Fin.last d) ∧
        (y = x + unit i ∨ y = x - unit i) ∧
        2 ≤ odoUnif (d + 1) (2 * M) (T + 1) y -
          odoUnif (d + 1) (2 * M) (T - 1) y ∧
        odoUnif (d + 1) (2 * M) (T + 1) y =
          odoUnif d (2 * M) (T + 1) z ∧
        odoUnif (d + 1) (2 * M) (T - 1) y =
          odoUnif d (2 * M) (T - 1) z) :
    simplexMax (d + 1) M (fun x =>
      odoUnif (d + 1) (2 * M) (t + 2) x -
        odoUnif (d + 1) (2 * M) t x) ≤ 1 := by
  obtain ⟨T, hT, hTt⟩ := (WithTop.le_coe_iff).mp ht
  have hTpos : 1 ≤ T := by
    have htop := one_le_toppleTime (d + 1) (M - 1)
    have htop' : (1 : ℕ∞) ≤ (T : ℕ∞) := by
      calc
        (1 : ℕ∞) ≤ toppleTime (d + 1) (M - 1) := htop
        _ = (T : ℕ∞) := hT
    exact ENat.coe_le_coe.mp htop'
  have hlowerT := (hlower_time T hT).1
  have hlowerTpred := (hlower_time T hT).2
  have hno1 : ∀ y : Site d, inSimplex d M y →
      2 ≤ odoUnif (d + 1) (2 * M) (T + 2) (Fin.snoc y 1) -
        odoUnif (d + 1) (2 * M) T (Fin.snoc y 1) → False := by
    intro y hy hbad
    have hredT := hred T hT y hy
    have hleastT := hleast T hT y hy
    have hbad' : 2 ≤ odoUnif d (2 * M) (T + 2) y -
        odoUnif d (2 * M) T y := by
      linarith [hbad, hleastT, hredT]
    have hpoint := le_simplexMax d M (fun z =>
      odoUnif d (2 * M) (T + 2) z - odoUnif d (2 * M) T z) y hy
    have hmax := hlower T hlowerT
    linarith
  have hbase : ∀ x : Site (d + 1), inSimplex (d + 1) M x →
      2 ≤ odoUnif (d + 1) (2 * M) (T + 2) x -
        odoUnif (d + 1) (2 * M) T x → False := by
    intro x hx hbad
    have hxlast : 1 ≤ x (Fin.last d) := (hx.1 (Fin.last d)).1
    have hcases : x (Fin.last d) = 1 ∨ x (Fin.last d) = 2 ∨
        3 ≤ x (Fin.last d) := by omega
    rcases hcases with hx1 | hx2 | hx3
    · let y : Site d := Fin.init x
      have hxy : Fin.snoc y 1 = x := by
        dsimp [y]
        rw [← hx1]
        exact Fin.snoc_init_self x
      have hy : inSimplex d M y := by
        rw [← inSimplex_snoc_one (by omega : 1 ≤ M) y]
        rw [hxy]
        exact hx
      apply hno1 y hy
      rw [hxy]
      exact hbad
    · let y : Site d := Fin.init x
      have hxy : Fin.snoc y 2 = x := by
        dsimp [y]
        rw [← hx2]
        exact Fin.snoc_init_self x
      have hy : inSimplex d M y := by
        have hsnoc : inSimplex (d + 1) M (Fin.snoc y 2) := by rw [hxy]; exact hx
        exact (inSimplex_snoc (x := y) (c := 2)).mp hsnoc |>.1
      let y1 : Site (d + 1) := Fin.snoc y 1
      have hy1 : inSimplex (d + 1) M y1 := by
        dsimp [y1]
        exact (inSimplex_snoc_one (by omega : 1 ≤ M) y).mpr hy
      have hmem : inSimplex (d + 1) M (y1 + unit (Fin.last d)) := by
        dsimp [y1]
        rw [← snoc_add_unit_last]
        norm_num
        rw [hxy]
        exact hx
      have haxis' := haxis (T + 2) (by omega) y1 hy1 (Fin.last d) ∅
        (by simp) (by simp)
        (by simpa only [Finset.sum_empty, sub_zero] using hmem)
      have hreflectT := hreflect T hT y hy
      have hreflectT' : odoUnif (d + 1) (2 * M) T y1 =
          odoUnif (d + 1) (2 * M) T x := by
        dsimp [y1]
        calc
          odoUnif (d + 1) (2 * M) T (Fin.snoc y 1) =
              odoUnif (d + 1) (2 * M) T
                (Fin.snoc y 1 + unit (Fin.last d)) := hreflectT
          _ = odoUnif (d + 1) (2 * M) T (Fin.snoc y 2) := by
            rw [← snoc_add_unit_last]
            norm_num
          _ = odoUnif (d + 1) (2 * M) T x := by rw [hxy]
      have haxis'' : odoUnif (d + 1) (2 * M) (T + 2) x ≤
          odoUnif (d + 1) (2 * M) (T + 2) y1 := by
        calc
          odoUnif (d + 1) (2 * M) (T + 2) x =
              odoUnif (d + 1) (2 * M) (T + 2) (Fin.snoc y 2) := by rw [hxy]
          _ = odoUnif (d + 1) (2 * M) (T + 2)
              (Fin.snoc y 1 + unit (Fin.last d)) := by
            rw [← snoc_add_unit_last]
            norm_num
          _ ≤ odoUnif (d + 1) (2 * M) (T + 2) y1 := by
            simpa only [Finset.sum_empty, sub_zero] using haxis'
      have hbad' : 2 ≤ odoUnif (d + 1) (2 * M) (T + 2) y1 -
          odoUnif (d + 1) (2 * M) T y1 := by
        linarith [hbad, hreflectT', haxis'']
      exact hno1 y hy (by simpa [y1] using hbad')
    · obtain ⟨y, z, _i, hy, hz, _hylast, _hneigh, hbad', hplus, hminus⟩ :=
        hneighbor T hT x hx hx3 hbad
      have hlowbad : 2 ≤ odoUnif d (2 * M) (T + 1) z -
          odoUnif d (2 * M) (T - 1) z := by
        rw [← hplus, ← hminus]
        exact hbad'
      have hpoint := le_simplexMax d M (fun w =>
        odoUnif d (2 * M) ((T - 1) + 2) w -
          odoUnif d (2 * M) (T - 1) w) z hz
      have hmax := hlower (T - 1) hlowerTpred
      rw [show T - 1 + 2 = T + 1 by omega] at hpoint hmax
      linarith
  have hbase' := Frozen.topple_limit (d + 1) M (by omega)
    (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
    (fun _ _ => by omega) (fun _ _ => by omega)
    (isSymmetricPile_const' (d + 1) (2 * M) (2 * ((d + 1 : ℕ) : ℤ))) T t 2 hTt
  have hbase'' : simplexMax (d + 1) M (fun x =>
      odoUnif (d + 1) (2 * M) (t + 2) x -
        odoUnif (d + 1) (2 * M) t x) ≤
      simplexMax (d + 1) M (fun x =>
        odoUnif (d + 1) (2 * M) (T + 2) x -
          odoUnif (d + 1) (2 * M) T x) := by
    simpa [odoUnif] using hbase'
  refine le_trans hbase'' ?_
  refine simplexMax_le (d + 1) M _ 1 (by norm_num) ?_
  intro x hx
  by_contra hbad
  have hbad' : 2 ≤ odoUnif (d + 1) (2 * M) (T + 2) x -
      odoUnif (d + 1) (2 * M) T x := by omega
  exact hbase x hx hbad'

end DimRed
