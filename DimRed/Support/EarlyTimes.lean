import DimRed.Support.Stabilize

/-!
The first two parallel toppling steps for the constant initial sandpile, and
the elementary bounds on its odometer used later in the reduction argument;
see the proof of the proposition (`base_dimension`) and the section labelled `sec:dim_reduction` in `dimred-corrected-arxiv.tex`.
-/
namespace DimRed

open LatticeProb

/-- Every site of the cube topples in the first parallel step. -/
theorem odoUnif_one (d N : ℕ) (_hd : 1 ≤ d) (x : Site d) (hx : inCube d N x) :
    odoUnif d N 1 x = 1 := by
  simp only [odoUnif, odo, if_pos hx]
  simp [lap, nbrSum]

/-- The first-step odometer vanishes outside the cube. -/
theorem odoUnif_one_outside (d N : ℕ) (x : Site d) (hx : ¬ inCube d N x) :
    odoUnif d N 1 x = 0 := by
  exact odo_eq_zero_outside d N (fun _ => 2 * (d : ℤ)) 1 x hx

/-- In the second step, an interior site topples again and a boundary site does not. -/
theorem odoUnif_two (d M : ℕ) (_hd : 1 ≤ d) (_hM : 2 ≤ M) (x : Site d)
    (hx : inCube d (2 * M) x) :
    odoUnif d (2 * M) 2 x =
      if ∀ i : Fin d, inCube d (2 * M) (x + unit i) ∧
          inCube d (2 * M) (x - unit i) then 2 else 1 := by
  have hU1 : ∀ y : Site d,
      odo d (2 * M) (fun _ => 2 * (d : ℤ)) 1 y =
        if inCube d (2 * M) y then 1 else 0 := by
    intro y
    by_cases hy : inCube d (2 * M) y
    · rw [if_pos hy]
      exact odoUnif_one d (2 * M) _hd y hy
    · rw [if_neg hy]
      exact odoUnif_one_outside d (2 * M) y hy
  have hsand : sandp d (2 * M) (fun _ => 2 * (d : ℤ)) 1 x =
      nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x := by
    simp only [sandp, lap]
    rw [show odo d (2 * M) (fun _ => 2 * (d : ℤ)) 1 =
        (fun y => if inCube d (2 * M) y then 1 else 0) from funext hU1]
    simp only [if_pos hx]
    ring
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) 2 x = _
  rw [odo_succ_eq d (2 * M) (fun _ => 2 * (d : ℤ)) 1 x hx,
    show odo d (2 * M) (fun _ => 2 * (d : ℤ)) 1 x = 1 from
      odoUnif_one d (2 * M) _hd x hx, hsand]
  by_cases hall : ∀ i : Fin d,
      inCube d (2 * M) (x + unit i) ∧ inCube d (2 * M) (x - unit i)
  · have hsum : nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x =
        2 * (d : ℤ) := by
      calc
        nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x =
            ∑ i : Fin d,
              ((if inCube d (2 * M) (x + unit i) then (1 : ℤ) else 0) +
                (if inCube d (2 * M) (x - unit i) then (1 : ℤ) else 0)) := by
          rfl
        _ = ∑ _i : Fin d, (2 : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          obtain ⟨hplus, hminus⟩ := hall i
          simp [hplus, hminus]
        _ = 2 * (d : ℤ) := by simp [Finset.sum_const, Finset.card_univ]; ring
    rw [hsum]
    simp [hall]
  · have hnotall : ¬ ∀ i : Fin d,
        inCube d (2 * M) (x + unit i) ∧ inCube d (2 * M) (x - unit i) := hall
    simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    have hmissing : ¬ inCube d (2 * M) (x + unit i) ∨
        ¬ inCube d (2 * M) (x - unit i) := by
      by_cases hplus : inCube d (2 * M) (x + unit i)
      · right
        intro hminus
        exact hi ⟨hplus, hminus⟩
      · exact Or.inl hplus
    have hlt : nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x <
        2 * (d : ℤ) := by
      have hsum :
          (∑ k : Fin d,
            ((if inCube d (2 * M) (x + unit k) then 1 else 0) +
              (if inCube d (2 * M) (x - unit k) then 1 else 0))) <
            ∑ _k : Fin d, (2 : ℤ) := by
        have hle : ∀ k : Fin d,
            (if inCube d (2 * M) (x + unit k) then (1 : ℤ) else 0) +
                (if inCube d (2 * M) (x - unit k) then (1 : ℤ) else 0) ≤ 2 := by
          intro k
          split_ifs <;> omega
        have hlt_i :
            (if inCube d (2 * M) (x + unit i) then (1 : ℤ) else 0) +
                (if inCube d (2 * M) (x - unit i) then (1 : ℤ) else 0) < 2 := by
          rcases hmissing with hplus | hminus
          · simp only [if_neg hplus]
            split_ifs <;> omega
          · simp only [if_neg hminus]
            split_ifs <;> omega
        exact Finset.sum_lt_sum (fun k _ => hle k)
          ⟨i, Finset.mem_univ i, hlt_i⟩
      calc
        nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x =
            ∑ k : Fin d,
              ((if inCube d (2 * M) (x + unit k) then (1 : ℤ) else 0) +
                (if inCube d (2 * M) (x - unit k) then (1 : ℤ) else 0)) := by
          rfl
        _ < ∑ _k : Fin d, (2 : ℤ) := hsum
        _ = 2 * (d : ℤ) := by simp [Finset.sum_const, Finset.card_univ]; ring
    have hnot : ¬ 2 * (d : ℤ) ≤
        nbrSum (fun y => if inCube d (2 * M) y then 1 else 0) x := not_le_of_gt hlt
    simp [hnotall, hnot]

/-- Every site in the cube has toppled at least once after the first step. -/
theorem one_le_odoUnif (d N : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) (x : Site d)
    (hx : inCube d N x) : 1 ≤ odoUnif d N t x := by
  have hone := odoUnif_one d N hd x hx
  calc
    (1 : ℤ) = odoUnif d N 1 x := hone.symm
    _ ≤ odoUnif d N t x := odo_mono d N (fun _ => 2 * (d : ℤ)) ht x

/-- No site can topple more than once per parallel step. -/
theorem odoUnif_le_self (d N t : ℕ) (x : Site d) :
    odoUnif d N t x ≤ (t : ℤ) := by
  induction t with
  | zero => simp [odoUnif, odo]
  | succ n ih =>
      have hstep := (odo_succ_sub_bounds d N (fun _ => 2 * (d : ℤ)) n x).2
      change odo d N (fun _ => 2 * (d : ℤ)) (n + 1) x ≤ (n : ℤ) + 1
      change odo d N (fun _ => 2 * (d : ℤ)) n x ≤ (n : ℤ) at ih
      linarith

end DimRed
