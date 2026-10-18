/-
The closed Case 2 export of the odometer strict-head and compatibility clauses.

The wrapper sits above the joint induction `reg_proved` and consumes its output together with
`odo_pure_diff`, `strong_raw_stay` and `strong_raw`.
The first clause is the pure second difference `odo_pure_diff` at horizon `t`, fed with the
weak and strong facet clauses of `reg_proved` at every time.  The second clause is the
same-time strong facet compatibility `strong_raw_stay` and `strong_raw` at `t`.
-/
import DimRed.Support.RegProved
import DimRed.Support.RegBridges
import DimRed.Support.StrongDerivRaw
import DimRed.Support.Case2FirstWait

open LatticeProb

/-- The strong-head and compatibility clauses on the positive orthant, at every dimension,
side, and time `t`, as exported from `reg_proved`. -/
theorem DimRed.case2_odo_strict_head_and_compat
    (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) :
    (∀ (k : Fin d) (x : Site d), case2Pos d M x →
      (∃ l : Fin d, x k < x l) →
      odoUnif d (2 * M) t x -
        odoUnif d (2 * M) t (x + unit k + unit k) ≤ 2 * x k) ∧
    (∀ (k : Fin d) (x : Site d), case2Pos d M x →
      x k = 1 → (∃ l : Fin d, 2 ≤ x l) →
      odoUnif d (2 * M) t x =
        odoUnif d (2 * M) t (x + unit k) + 1 →
      odoUnif d (2 * M) (t + 1) x = odoUnif d (2 * M) t x ∧
      odoUnif d (2 * M) (t + 1) (x + unit k) =
        odoUnif d (2 * M) t (x + unit k) + 1) := by
  have hpos : ∀ x : Site d, case2Pos d M x → inPos d M x := by
    intro x hx
    unfold case2Pos at hx
    unfold inPos
    exact hx
  -- `Reg d M s` unfolds to `RegConsist ∧ RegWeak ∧ RegStrongDeriv ∧ RegStrongFacet ∧ RegTopple`.
  have hW : ∀ s, 1 ≤ s → s < t → RegWeak d M s :=
    fun s _ _ => (reg_proved d M s hd hM).1.2.1
  have hS : ∀ s, s < t → RegStrongFacet d M s :=
    fun s _ => (reg_proved d M s hd hM).1.2.2.2.1
  have hC := odo_pure_diff d M t hd (by omega) hW hS t le_rfl
  have hSt : RegStrongFacet d M t := (reg_proved d M t hd hM).1.2.2.2.1
  constructor
  · intro k x hx hmax
    exact hC k x (hpos x hx) hmax
  · intro k x hx hk h2 h
    have hpx := hpos x hx
    exact ⟨strong_raw_stay d M t hSt x hpx k hk h2 h, strong_raw d M t hSt x hpx k hk h2 h⟩

/-- The concrete point `(1, 2)` of the square `{1, 2}²`, the witness of the nonvacuity check. -/
def DimRed.case2ClosedPoint : Site 2 := ![1, 2]

theorem DimRed.case2ClosedPoint_pos : case2Pos 2 2 case2ClosedPoint := by
  unfold case2Pos case2ClosedPoint
  intro i
  fin_cases i <;> decide

/-- Nonvacuity: the first clause of `case2_odo_strict_head_and_compat` at `d = 2`, `M = 2`,
`t = 3`, the positive point `p = (1, 2)`, `k = 0`, with the witness `l = 1` where `p 0 < p 1`. -/
theorem DimRed.case2_closed_nonvacuity :
    odoUnif 2 (2 * 2) 3 case2ClosedPoint -
      odoUnif 2 (2 * 2) 3 (case2ClosedPoint + unit (0 : Fin 2) + unit (0 : Fin 2)) ≤
        2 * case2ClosedPoint 0 :=
  (case2_odo_strict_head_and_compat 2 2 3 (by norm_num) (by norm_num)).1 0 case2ClosedPoint
    case2ClosedPoint_pos ⟨1, by decide⟩

/-- Nonvacuity: the second clause of `case2_odo_strict_head_and_compat` at `d = 2`, `M = 2`,
`t = 3`, the positive point `p = (1, 2)`, `k = 0`, with the witness `l = 1` where `2 ≤ p 1`.
The gap hypothesis `odo_3(1, 2) = odo_3(2, 2) + 1` holds by evaluation: `2 = 1 + 1`. -/
theorem DimRed.case2_closed_nonvacuity_compat :
    odoUnif 2 (2 * 2) (3 + 1) case2ClosedPoint = odoUnif 2 (2 * 2) 3 case2ClosedPoint ∧
      odoUnif 2 (2 * 2) (3 + 1) (case2ClosedPoint + unit (0 : Fin 2)) =
        odoUnif 2 (2 * 2) 3 (case2ClosedPoint + unit (0 : Fin 2)) + 1 := by
  have hgap : odoUnif 2 (2 * 2) 3 case2ClosedPoint =
      odoUnif 2 (2 * 2) 3 (case2ClosedPoint + unit (0 : Fin 2)) + 1 := by
    decide
  exact (case2_odo_strict_head_and_compat 2 2 3 (by norm_num) (by norm_num)).2 0 case2ClosedPoint
    case2ClosedPoint_pos (by rfl) ⟨1, by decide⟩ hgap
