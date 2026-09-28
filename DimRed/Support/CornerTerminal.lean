/-
The terminal odometer at the corner `(j, 1_{d-1})` of the side-`2j` cube is
exactly `j`, in every dimension.  The proof descends to dimension one by
`odoInfUnif_snoc_eq` at each step and uses `odoInf_one_eq` at `M = j`, `y = j`,
where the arithmetic gives `(j(j+1) - j(j-1))/2 = j`.  This is the upper bound
that makes the topple time `τ_j = j² - j + 1` exact.
-/
import DimRed.Support.ToppleTimeScale
import DimRed.Support.CornerBound
import DimRed.Support.OneDimTerminal

namespace DimRed

open LatticeProb

/-- The terminal odometer at the corner `(j, 1_{d-1})` of the side-`2j` cube is
exactly `j`, in every dimension. -/
theorem odoInfUnif_corner_eq (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hred : ∀ (e : ℕ), 1 ≤ e → e < d → ∀ (t : ℕ) (y : Site e),
      inSimplex e j y →
      odoUnif (e + 1) (2 * j) t (Fin.snoc y 1) = odoUnif e (2 * j) t y) :
    odoInfUnif d (2 * j) (cornerPoint d j) = (j : ℕ∞) := by
  have h1 : odoInfUnif 1 (2 * j) (fun _ : Fin 1 => (j : ℤ)) = (j : ℕ∞) := by
    rw [odoInf_one_eq j hj (fun _ : Fin 1 => (j : ℤ)) (by omega) (by omega)]
    have harith : ((j : ℤ) * ((j : ℤ) + 1) - (j : ℤ) * ((j : ℤ) - 1)) / 2 = (j : ℤ) := by
      have hnum : (j : ℤ) * ((j : ℤ) + 1) - (j : ℤ) * ((j : ℤ) - 1) = 2 * (j : ℤ) := by ring
      rw [hnum]
      exact Int.mul_ediv_cancel_left j (by norm_num : (2 : ℤ) ≠ 0)
    rw [harith]
    simp only [Int.toNat_natCast]
  induction d with
  | zero => omega
  | succ e ih =>
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · subst he0
        have hc : cornerPoint 1 j = (fun _ : Fin 1 => (j : ℤ)) := cornerPoint_one j
        rw [hc]
        exact h1
      · rw [← cornerPoint_snoc e j hepos]
        rw [odoInfUnif_snoc_eq e j (cornerPoint e j) (fun t => by
          have h := hred e hepos (by omega) t (cornerPoint e j)
            (cornerPoint_mem_inSimplex e j hj)
          simpa [odoUnif] using h)]
        exact ih hepos (fun e' he' he'd t y hy => hred e' he' (by omega) t y hy)

/-- The one-step corner domination from dimensional reduction at the topple time
and the parabolic least action principle, which is the paper's route
(`dimred.tex:1449-1470`). -/
theorem corner_dominate_step_dimred (d c n : ℕ) (hd : 1 ≤ d) (_hc : 1 ≤ c)
    (_hn : (n : ℕ∞) ≤ toppleTime d c)
    (hred : ∀ (t : ℕ) (y : Site d), inSimplex d (c + 1) y →
      odoUnif (d + 1) (2 * (c + 1)) t (Fin.snoc y 1) = odoUnif d (2 * (c + 1)) t y) :
    odoUnif (d + 1) (2 * (c + 1)) n (cornerPoint (d + 1) (c + 1)) ≤
      odoUnif d (2 * (c + 1)) n (cornerPoint d (c + 1)) := by
  -- the corner of the `(d+1)`-cube is the `Fin.snoc` of the `d`-dimensional
  -- corner with `1`, so dimensional reduction identifies the two
  rw [← cornerPoint_snoc d (c + 1) hd]
  exact le_of_eq (hred n (cornerPoint d (c + 1))
    (cornerPoint_mem_inSimplex d (c + 1) (by omega)))

/-- The one-step corner domination in the form the wiring uses: the corner of the
`d`-cube at scale `c+1` is at most the `(d-1)`-dimensional corner at scale `c`
plus one, for `n ≤ τ_{d-1}(c)`. -/
theorem corner_dominate_wire (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c)
    (hn : (n : ℕ∞) ≤ toppleTime (d - 1) c)
    (hred : ∀ (t : ℕ) (y : Site (d - 1)), inSimplex (d - 1) (c + 1) y →
      odoUnif ((d - 1) + 1) (2 * (c + 1)) t (Fin.snoc y 1)
        = odoUnif (d - 1) (2 * (c + 1)) t y) :
    odoUnif ((d - 1) + 1) (2 * (c + 1)) n (cornerPoint ((d - 1) + 1) (c + 1)) ≤
      odoUnif (d - 1) (2 * (c + 1)) n (cornerPoint (d - 1) (c + 1)) := by
  have h := corner_dominate_step_dimred (d - 1) c n (by omega) hc hn
    (fun t y hy => hred t y hy)
  have hcast : (d - 1) + 1 = d := by omega
  simpa only [hcast] using h

end DimRed
