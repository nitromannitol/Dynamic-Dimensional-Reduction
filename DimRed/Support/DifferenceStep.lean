/-
The two steps of the induction in Lemma 2.4 of `dimred.tex:473-492`: the
interior step, where every neighbour of `x` and of `x + w` is again a site of
the domain and the recursion of Lemma 2.1 applies at both, and the boundary
step, where the first branch of `eq:boundaries_ref` bounds the neighbour sums
directly.  Both are floor-division computations on `ℤ`.
-/
import DimRed.Support.NonnegativeUpdate
import DimRed.Support.Difference

namespace DimRed

open LatticeProb


theorem difference_interior_step (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (w : Site d) (g : Site d → ℤ) (hg : SuperharmonicIn d M g)
    (n : ℕ) (x : Site d) (hx : inSimplex d M x)
    (hx0 : ∀ i : Fin d, inSimplex d M (x + unit i) ∧ inSimplex d M (x - unit i))
    (_hxw : ∀ i : Fin d, inSimplex d M (x + w + unit i) ∧ inSimplex d M (x + w - unit i))
    (hcube : inCube d (2 * M) (x + w))
    (hih : ∀ y, inSimplex d M y →
      odo d (2 * M) (fun _ => c) n y - odo d (2 * M) (fun _ => c) n (y + w) - g y ≤ 0) :
    odo d (2 * M) (fun _ => c) (n + 1) x - odo d (2 * M) (fun _ => c) (n + 1) (x + w) - g x ≤ 0 := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hc0' : ∀ y, inCube d (2 * M) y → 0 ≤ (fun _ => c) y := fun y _ => hc0
  have hc1' : ∀ y, inCube d (2 * M) y → (fun _ => c) y ≤ 2 * (2 * (d : ℤ)) - 1 := fun y _ => hc1
  have hx_cube : inCube d (2 * M) x := inSimplex_inCube d M x hx
  have hA := DimRed.bounded_point_update d (2 * M) hd (fun _ => c) hc0' hc1' n x hx_cube
  have hB := DimRed.bounded_point_update d (2 * M) hd (fun _ => c) hc0' hc1' n (x + w) hcube
  have hshift : DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w)
      = DimRed.nbrSum (fun y => odo d (2 * M) (fun _ => c) n (y + w)) x :=
    (nbrSum_shift (odo d (2 * M) (fun _ => c) n) x w).symm
  have hsub : DimRed.nbrSum (fun y => odo d (2 * M) (fun _ => c) n y
        - odo d (2 * M) (fun _ => c) n (y + w)) x
      = DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
        - DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w) := by
    rw [nbrSum_sub, hshift]
  have hsum_le : DimRed.nbrSum (fun y => odo d (2 * M) (fun _ => c) n y
        - odo d (2 * M) (fun _ => c) n (y + w)) x ≤ DimRed.nbrSum g x := by
    simp only [DimRed.nbrSum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hih (x + unit i) (hx0 i).1
    have h2 := hih (x - unit i) (hx0 i).2
    linarith
  have hsuper := hg x hx hx0
  have hfloor : odo d (2 * M) (fun _ => c) (n + 1) x - odo d (2 * M) (fun _ => c) (n + 1) (x + w)
      ≤ (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
          - (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w)) + ((2 * d : ℕ) : ℤ) - 1) / ((2 * d : ℕ) : ℤ) := by
    rw [hA, hB]
    push_cast
    exact ediv_sub_ediv_le _ _ (2 * d) (by omega)
  have hkey : c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
      - (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w))
      ≤ 2 * (d : ℤ) * g x := by
    have := hsum_le
    have := hsuper
    linarith
  have hfinal := ediv_le_of_le_mul _ (g x) (2 * d) (by omega) hkey
  linarith

/-- The boundary step of the induction: the first branch of `eq:boundaries_ref`
bounds the neighbour sums at time `n`, and the floor division turns that into
the bound on the difference of the odometers at time `n + 1`. -/
theorem difference_boundary_step (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (w : Site d) (g : Site d → ℤ)
    (n : ℕ) (x : Site d) (hx : inSimplex d M x)
    (hcube : inCube d (2 * M) (x + w))
    (hbd : DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
      - DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w) - 2 * (d : ℤ) * g x ≤ 0) :
    odo d (2 * M) (fun _ => c) (n + 1) x - odo d (2 * M) (fun _ => c) (n + 1) (x + w) - g x ≤ 0 := by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hc0' : ∀ y, inCube d (2 * M) y → 0 ≤ (fun _ => c) y := fun y _ => hc0
  have hc1' : ∀ y, inCube d (2 * M) y → (fun _ => c) y ≤ 2 * (2 * (d : ℤ)) - 1 := fun y _ => hc1
  have hx_cube : inCube d (2 * M) x := inSimplex_inCube d M x hx
  have hA := DimRed.bounded_point_update d (2 * M) hd (fun _ => c) hc0' hc1' n x hx_cube
  have hB := DimRed.bounded_point_update d (2 * M) hd (fun _ => c) hc0' hc1' n (x + w) hcube
  have hfloor : odo d (2 * M) (fun _ => c) (n + 1) x - odo d (2 * M) (fun _ => c) (n + 1) (x + w)
      ≤ (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
          - (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w)) + ((2 * d : ℕ) : ℤ) - 1) / ((2 * d : ℕ) : ℤ) := by
    rw [hA, hB]
    push_cast
    exact ediv_sub_ediv_le _ _ (2 * d) (by omega)
  have hkey : c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) x
      - (c + DimRed.nbrSum (odo d (2 * M) (fun _ => c) n) (x + w))
      ≤ 2 * (d : ℤ) * g x := by
    linarith
  have hfinal := ediv_le_of_le_mul _ (g x) (2 * d) (by omega) hkey
  linarith

end DimRed
