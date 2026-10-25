module

/-
The topple time exists.  `DimRed/Support/ToppleTime.lean` reduces its existence to the
odometer at the corner `(j, 1_{d-1})` of `C_{2j}^{(d)}` reaching height `j`; that is proved
here, by descending to dimension one, where `odoInf_one_eq` gives the terminal value
`(j(j+1) - j(j-1))/2 = j` exactly.  The bound is sharp: the corner reaches `j` and never
exceeds it, so nothing weaker than the exact one-dimensional value would do.

The descent uses dimensional reduction in every lower dimension, which is an earlier instance
of the induction of Sections 4 and 5, carried here as `hdimred`.
-/
public import DimRed.Support.ToppleTime
public import DimRed.Support.OneDimTerminal
public import DimRed.Support.EarlyTimes

@[expose] public section

namespace DimRed

open LatticeProb

/-- The corner point lies in the simplex. -/
lemma cornerPoint_mem_inSimplex (d M : ℕ) (hM : 1 ≤ M) : inSimplex d M (cornerPoint d M) := by
  constructor
  · intro i
    rw [cornerPoint]
    split
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · intro a b _
    rw [cornerPoint, cornerPoint]
    split <;> split <;> omega

/-- `Fin.snoc` of a corner point with `1` is the corner point in one higher dimension. -/
lemma cornerPoint_snoc (d j : ℕ) (hd : 1 ≤ d) : Fin.snoc (cornerPoint d j) (1 : ℤ) = cornerPoint (d + 1) j := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [cornerPoint]
    omega
  · simp [cornerPoint]

/-- The odometer at the corner `(j, 1_{d-1})` of `C_{2j}^{(d)}` reaches height `j`,
which is what makes the topple time exist.  Measured: the terminal value at that
corner is exactly `j` in every dimension, so the bound is sharp. -/
theorem corner_reaches (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hdimred : ∀ e : ℕ, 1 ≤ e → e < d → ∀ (t : ℕ) (y : Site e), inSimplex e j y →
      odoUnif (e + 1) (2 * j) t (Fin.snoc y 1) = odoUnif e (2 * j) t y) :
    ∃ n : ℕ, 1 ≤ n ∧ (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j) := by
  -- The corner is in the simplex in dimension 1
  have hsimp1 : inSimplex 1 j (cornerPoint 1 j) :=
    cornerPoint_mem_inSimplex 1 j hj
  -- Coordinates of the corner in dimension 1
  have hy0 : 1 ≤ (cornerPoint 1 j) 0 := by
    rw [cornerPoint]; omega
  have hyM : (cornerPoint 1 j) 0 ≤ (j : ℤ) := by
    rw [cornerPoint]; omega
  -- Terminal odometer at the corner in dimension 1 equals j
  have hterm : odoInfUnif 1 (2 * j) (cornerPoint 1 j) = (j : ℕ∞) := by
    rw [odoInf_one_eq j hj (cornerPoint 1 j) hy0 hyM]
    have hcalc : ((j : ℤ) * ((j : ℤ) + 1) - (j : ℤ) * ((j : ℤ) - 1)) / 2 = (j : ℤ) := by
      have hnum : (j : ℤ) * ((j : ℤ) + 1) - (j : ℤ) * ((j : ℤ) - 1) = 2 * (j : ℤ) := by ring
      rw [hnum]
      omega
    simp [cornerPoint, hcalc]
  -- The process stabilizes in dimension 1
  obtain ⟨T, hT⟩ := one_odo_stable j
  have hstable : odo 1 (2 * j) (fun _ => 2) (T + 1) = odo 1 (2 * j) (fun _ => 2) T := hT
  -- At stabilization time, the odometer equals the terminal value
  have hinf : odoInfUnif 1 (2 * j) (cornerPoint 1 j) =
      ((odo 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j)).toNat : ℕ∞) := by
    simpa [odoInfUnif] using odoInf_eq_of_stable 1 (2 * j) (fun _ => 2) T hstable (cornerPoint 1 j)
  rw [hterm] at hinf
  -- Extract the equality of natural numbers
  have hval_nat : (odo 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j)).toNat = j := by
    exact_mod_cast hinf.symm
  -- Since the odometer is nonnegative, this gives equality in ℤ
  have hnonneg : 0 ≤ odo 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j) :=
    odo_nonneg 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j)
  have hval_nat' : ((odo 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j)).toNat : ℤ) = (j : ℤ) := by
    exact_mod_cast hval_nat
  have hval : odoUnif 1 (2 * j) T (cornerPoint 1 j) = (j : ℤ) := by
    dsimp [odoUnif]
    rw [← Int.toNat_of_nonneg hnonneg, hval_nat']
  -- So in dimension 1, the odometer at time T is already j
  have hone_dim : (j : ℤ) ≤ odoUnif 1 (2 * j) T (cornerPoint 1 j) :=
    hval.symm.le
  -- Ensure the time index is at least 1
  let n := max T 1
  have hnpos : 1 ≤ n := le_max_right _ _
  -- The odometer is monotone in time, so it stays ≥ j from time T onward
  have hone_dim_n : (j : ℤ) ≤ odoUnif 1 (2 * j) n (cornerPoint 1 j) := by
    have hTn : T ≤ n := le_max_left _ _
    have hmono := odo_mono 1 (2 * j) (fun _ => 2) hTn (cornerPoint 1 j)
    -- hmono : odo 1 (2 * j) (fun _ => 2) T (cornerPoint 1 j) ≤
    --         odo 1 (2 * j) (fun _ => 2) n (cornerPoint 1 j)
    have hmono' : odoUnif 1 (2 * j) T (cornerPoint 1 j) ≤ odoUnif 1 (2 * j) n (cornerPoint 1 j) := by
      simpa [odoUnif] using hmono
    exact le_trans hone_dim hmono'
  -- Now lift from dimension 1 to dimension d using hdimred
  -- Iterate hdimred from dimension d down to 1
  have hiter : odoUnif d (2 * j) n (cornerPoint d j) = odoUnif 1 (2 * j) n (cornerPoint 1 j) := by
    induction' d using Nat.strong_induction_on with d ih
    rcases Nat.eq_or_lt_of_le hd with (rfl | hd_gt)
    · rfl
    · have hd1 : 1 ≤ d - 1 := by omega
      have hlt : d - 1 < d := by omega
      have hred := hdimred (d - 1) hd1 hlt n (cornerPoint (d - 1) j)
        (cornerPoint_mem_inSimplex (d - 1) j hj)
      rw [cornerPoint_snoc (d - 1) j hd1] at hred
      have hd_eq : (d - 1 : ℕ) + 1 = d := Nat.sub_add_cancel (by omega)
      rw [hd_eq] at hred
      rw [hred]
      apply ih (d - 1) hlt hd1
      intro e he1 helt
      exact hdimred e he1 (lt_of_lt_of_le helt (by omega))
  refine ⟨n, hnpos, ?_⟩
  rw [hiter]
  exact hone_dim_n

/-- The topple time is monotone in the dimension, given dimensional reduction at
the corner: the corner of the smaller cube reaches height `j` no later than the
corner of the larger one. -/
theorem toppleTime_mono_dim (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hred : ∀ (t : ℕ) (y : Site d), inSimplex d j y →
      odoUnif (d + 1) (2 * j) t (Fin.snoc y 1) = odoUnif d (2 * j) t y)
    (hred' : ∀ (e : ℕ), 1 ≤ e → e < d + 1 → ∀ (t : ℕ) (y : Site e),
      inSimplex e j y →
      odoUnif (e + 1) (2 * j) t (Fin.snoc y 1) = odoUnif e (2 * j) t y) :
    toppleTime d j ≤ toppleTime (d + 1) j := by
  have hhit : ∃ n : ℕ, 1 ≤ n ∧
      (j : ℤ) ≤ odoUnif (d + 1) (2 * j) n (cornerPoint (d + 1) j) :=
    corner_reaches (d + 1) j (by omega) hj (fun e he hed t y hy => by
      -- the reduction in dimension `e+1` at scale `j` is the corner identity of
      -- the smaller dimension, which is the induction hypothesis at `e`
      exact hred' e he hed t y hy)
  have hbig := (toppleTime_le_iff (d + 1) j (by omega) hj hhit
    (toppleTime (d + 1) j)).mp (le_refl _)
  obtain ⟨n, hn, hn1, hval⟩ := hbig
  have hc : inSimplex d j (cornerPoint d j) := cornerPoint_mem_inSimplex d j hj
  have hsmall : (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j) := by
    rw [← hred n (cornerPoint d j) hc, cornerPoint_snoc d j hd]
    exact hval
  refine (toppleTime_le_iff d j hd hj ⟨n, hn1, hsmall⟩ (toppleTime (d + 1) j)).mpr
    ⟨n, hn, hn1, hsmall⟩

/-- At scale one the corner of the cube has already toppled once at the first
step, in every dimension. -/
theorem corner_one_le (d : ℕ) :
    (1 : ℤ) ≤ odoUnif d 2 1 (cornerPoint d 1) := by
  have hc : inCube d 2 (cornerPoint d 1) := by
    intro i
    rw [cornerPoint]
    split <;> simp [loCoord, hiCoord, sideHalf]
  simp only [odoUnif]
  rw [odo_succ_eq d 2 (fun _ => 2 * (d : ℤ)) 0 (cornerPoint d 1) hc]
  have hzero : odo d 2 (fun _ => 2 * (d : ℤ)) 0 (cornerPoint d 1) = 0 := rfl
  rw [hzero]
  have hsand : sandp d 2 (fun _ => 2 * (d : ℤ)) 0 (cornerPoint d 1) = 2 * (d : ℤ) := by
    simp [sandp, lap, odo, nbrSum]
  rw [hsand]
  norm_num

/-- The reverse dimension monotonicity of the topple time, from dimensional
reduction at the corner. -/
theorem toppleTime_mono_dim_le (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    (hred : ∀ (t : ℕ) (y : Site d), inSimplex d j y →
      odoUnif (d + 1) (2 * j) t (Fin.snoc y 1) = odoUnif d (2 * j) t y)
    (hred' : ∀ (e : ℕ), 1 ≤ e → e < d + 1 → ∀ (t : ℕ) (y : Site e),
      inSimplex e j y →
      odoUnif (e + 1) (2 * j) t (Fin.snoc y 1) = odoUnif e (2 * j) t y) :
    toppleTime (d + 1) j ≤ toppleTime d j := by
  have hhit : ∃ n : ℕ, 1 ≤ n ∧
      (j : ℤ) ≤ odoUnif d (2 * j) n (cornerPoint d j) :=
    corner_reaches d j hd hj (fun e he hed t y hy => hred' e he (by omega) t y hy)
  have hbig := (toppleTime_le_iff d j hd hj hhit (toppleTime d j)).mp (le_refl _)
  obtain ⟨n, hn, hn1, hval⟩ := hbig
  have hc : inSimplex d j (cornerPoint d j) := cornerPoint_mem_inSimplex d j hj
  have hbig' : (j : ℤ) ≤ odoUnif (d + 1) (2 * j) n (cornerPoint (d + 1) j) := by
    rw [← cornerPoint_snoc d j hd]
    rw [hred n (cornerPoint d j) hc]
    exact hval
  refine (toppleTime_le_iff (d + 1) j (by omega) hj ⟨n, hn1, hbig'⟩
    (toppleTime d j)).mpr ⟨n, hn, hn1, hbig'⟩

end DimRed
