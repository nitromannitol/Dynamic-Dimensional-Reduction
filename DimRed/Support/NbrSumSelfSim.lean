import DimRed.Support.ToppleTimeScale
import DimRed.Support.SelfSimilarityMain
import DimRed.Support.RegInduction
import DimRed.Support.SimplexFold
import DimRed.Support.Fundamental
import DimRed.Support.AxisStep
import DimRed.Support.FoldIdentity

open LatticeProb DimRed

namespace DimRed

/-- The neighbour-sum identity of Case 1 of the one-step self-similarity,
The subsection titled `Odometer regularity for d >= 2` in `dimred-corrected-arxiv.tex`: for `y ∈ S_m` with every coordinate above two, the
symmetrized neighbour sum of the odometer at scale `m` equals the symmetrized
neighbour sum at scale `m - 1` of `y - 1`, given the one-step identity at the
same time for every point of `S_m` with all coordinates above one. -/
theorem nbrSum_selfsim_step (d m t : ℕ) (_hd : 2 ≤ d) (hm : 3 ≤ m)
    (y : Site d) (hy : inSimplex d m y) (hygt : ∀ i : Fin d, 2 < y i)
    (hstep : ∀ z : Site d, inSimplex d m z → (∀ i : Fin d, 1 < z i) →
      odoUnif d (2 * m) t z = odoUnif d (2 * (m - 1)) t (fun i => z i - 1)) :
    nbrSum (odoUnif d (2 * m) t) y
      = nbrSum (odoUnif d (2 * (m - 1)) t) (fun i => y i - 1) := by
  -- every neighbour of `y` is in the cube and has all coordinates at least two,
  -- so its fold lies in `S_m` with all coordinates above one
  have hfold : ∀ z : Site d, inCube d (2 * m) z → (∀ k, 2 ≤ z k) →
      inSimplex d m (toSimplexPoint d m z) ∧
        (∀ k : Fin d, 1 < toSimplexPoint d m z k) := by
    intro z hz hz2
    refine ⟨inSimplex_toSimplexPoint d m z hz, fun k => ?_⟩
    have hmem := foldPoint_mem d m z hz k
    rw [toSimplexPoint]
    have hfold2 : 2 ≤ foldPoint d (2 * m) z
        (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k) := by
      rw [foldPoint_apply, if_pos (by have := hz2 (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k); omega)]
      exact hz2 _
    exact hfold2
  have hb : ∀ i k : Fin d, 2 ≤ (y + unit i) k ∧ 2 ≤ (y - unit i) k := by
    intro i k
    have h2 := hygt k
    by_cases hk : k = i
    · subst hk
      rw [add_unit_self, sub_unit_self]
      omega
    · rw [add_unit_other _ _ _ _ hk, sub_unit_other _ _ _ _ hk]
      omega
  have hc1 : ∀ i : Fin d, y i < (m : ℤ) → inCube d (2 * m) (y + unit i) := by
    intro i hi k
    have h1 := hy.1 k
    rw [loCoord_two_mul, hiCoord_two_mul]
    by_cases hk : k = i
    · subst hk
      rw [add_unit_self]
      constructor <;> omega
    · rw [add_unit_other _ _ _ _ hk]
      constructor <;> omega
  have hc2 : ∀ i : Fin d, inCube d (2 * m) (y - unit i) := by
    intro i k
    have h1 := hy.1 k
    rw [loCoord_two_mul, hiCoord_two_mul]
    by_cases hk : k = i
    · subst hk
      rw [sub_unit_self]
      omega
    · rw [sub_unit_other _ _ _ _ hk]
      omega
  have hterm : ∀ i : Fin d,
      odoUnif d (2 * m) t (y + unit i) + odoUnif d (2 * m) t (y - unit i)
        = odoUnif d (2 * (m - 1)) t (fun k => (y + unit i) k - 1)
          + odoUnif d (2 * (m - 1)) t (fun k => (y - unit i) k - 1) := by
    intro i
    obtain ⟨hf2, hg2⟩ := hfold (y - unit i) (hc2 i) (fun k => (hb i k).2)
    have h2 := hstep _ hf2 hg2
    rw [← odoUnif_toSimplexPoint d m t (y - unit i), h2,
      odoUnif_toSimplexPoint_sub d m t (y - unit i) (fun k => by have := (hb i k).2; omega)]
    by_cases hlt : y i < (m : ℤ)
    · obtain ⟨hf1, hg1⟩ := hfold (y + unit i) (hc1 i hlt) (fun k => (hb i k).1)
      have h1 := hstep _ hf1 hg1
      rw [← odoUnif_toSimplexPoint d m t (y + unit i), h1,
        odoUnif_toSimplexPoint_sub d m t (y + unit i) (fun k => by have := (hb i k).1; omega)]
    · -- `y i = m`: the `+unit` neighbour is off the cube, and so is its shift
      have hyi : y i = (m : ℤ) := by
        have h1 := hy.1 i
        omega
      have hout : odoUnif d (2 * m) t (y + unit i) = 0 := by
        rw [odoUnif, odo_eq_zero_outside]
        intro hc
        have h1 := hc i
        rw [loCoord_two_mul, hiCoord_two_mul, add_unit_self, hyi] at h1
        omega
      have hout' : odoUnif d (2 * (m - 1)) t (fun k => (y + unit i) k - 1) = 0 := by
        rw [odoUnif, odo_eq_zero_outside]
        intro hc
        have h1 := hc i
        rw [loCoord_two_mul, hiCoord_two_mul] at h1
        simp only at h1
        rw [add_unit_self, hyi] at h1
        omega
      rw [hout, hout']
  simp only [nbrSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i]
  congr 1 <;> (congr 1; funext k; simp only [Pi.add_apply, Pi.sub_apply]; ring)

end DimRed
