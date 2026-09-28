import DimRed.Support.RegBridges
import DimRed.Support.StrongDerivPure
import DimRed.Support.Recursion
import DimRed.Support.Stabilize
open LatticeProb DimRed
namespace DimRed

/-- The gap at time `q` implies the head point toppled at step `q`: if the head
`(z,1)` has one more topple than its neighbour `(z,2)` at time `q`, then the head
rose by one between `q-1` and `q`.

The argument: the first-difference bound gives
`v_{q-1}(head) - v_{q-1}(mid) ≤ 1`.  If the gap held at `q-1`, the toppling form
of strong facet compatibility at `q-1` would give `v_q(head) = v_{q-1}(head)` and
`v_q(mid) = v_{q-1}(mid) + 1`, hence `v_q(head) = v_q(mid) + 2`, contradicting the
gap at `q`.  So `v_{q-1}(head) ≤ v_{q-1}(mid)`.  Monotonicity in time gives
`v_q(mid) ≥ v_{q-1}(mid) ≥ v_{q-1}(head)`, and the gap at `q` gives
`v_q(head) = v_q(mid) + 1 ≥ v_{q-1}(head) + 1`; the one-step bound gives the
reverse inequality. -/
theorem odo_topple_of_gap (d M q : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (hq : 1 ≤ q)
    (hS : RegStrongFacet (d + 1) M (q - 1))
    (z : Site d) (hz : inSimplex d M z) (hz1 : ∀ k, 1 < z k)
    (hgap : odoUnif (d + 1) (2 * M) q (Fin.snoc z 1) =
      odoUnif (d + 1) (2 * M) q (Fin.snoc z 1 + unit (Fin.last d)) + 1) :
    odoUnif (d + 1) (2 * M) q (Fin.snoc z 1) =
      odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) + 1 := by
  have hX : inSimplex (d + 1) M (Fin.snoc z 1) :=
    inSimplex_snoc_one_local z hz (by omega)
  have hlast : (Fin.snoc z 1 : Site (d + 1)) (Fin.last d) = 1 := by
    simp [Fin.snoc]
  have h2 : ∃ l, 2 ≤ (Fin.snoc z 1 : Site (d + 1)) l :=
    ⟨Fin.castSucc ⟨0, by omega⟩, by
      simp only [Fin.snoc_castSucc]
      have := hz1 ⟨0, by omega⟩
      omega⟩
  have hpt : Fin.snoc z 1 + unit (Fin.last d) = Fin.snoc z 2 := by
    rw [← fin_snoc_add_last z 1]
    norm_num
  -- the first-difference bound at `q - 1`
  have hfd := odo_first_diff (d + 1) M (by omega) (by omega) (q - 1) (Fin.last d)
    (Fin.snoc z 1) (by simp [hlast])
  -- the one-step bound at `q`
  have hstep := (odo_succ_sub_bounds (d + 1) (2 * M)
    (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) (q - 1) (Fin.snoc z 1)).2
  rw [show q - 1 + 1 = q by omega] at hstep
  -- the head is at most the neighbour at `q - 1`
  have hprev_le : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) ≤
      odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1 + unit (Fin.last d)) := by
    by_cases hg : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) =
        odoUnif (d + 1) (2 * M) (q - 1)
          (Fin.snoc z 1 + unit (Fin.last d)) + 1
    · -- the gap at `q - 1` would force the head to stay and the neighbour to
      -- rise at `q`, contradicting the gap at `q`
      have htopple := strong_facet_step_topple_of_reg (d + 1) M (q - 1) hS
      have hres := (htopple (Fin.snoc z 1) (Fin.last d) hX hlast h2 hg).1
      rw [show q - 1 + 1 = q by omega] at hres
      have hmid := (htopple (Fin.snoc z 1) (Fin.last d) hX hlast h2 hg).2
      rw [show q - 1 + 1 = q by omega] at hmid
      omega
    · -- otherwise the first-difference bound gives it
      have h := hfd
      rw [hlast] at h
      omega
  -- monotonicity in time at the neighbour
  have hmono := odo_mono (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
    (show q - 1 ≤ q by omega) (Fin.snoc z 1 + unit (Fin.last d))
  -- the gap at `q` and the one-step bound at `q`
  have hstep' : odoUnif (d + 1) (2 * M) q (Fin.snoc z 1) ≤
      odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) + 1 := by
    have h := hstep
    simp only [odoUnif] at h ⊢
    omega
  -- `v_q(head) = v_q(mid) + 1 ≥ v_{q-1}(mid) + 1 ≥ v_{q-1}(head) + 1`
  have hchain : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) + 1 ≤
      odoUnif (d + 1) (2 * M) q (Fin.snoc z 1) := by
    have h1 : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1) + 1 ≤
        odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1 + unit (Fin.last d)) + 1 := by
      omega
    have h2 : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1 + unit (Fin.last d)) + 1 ≤
        odoUnif (d + 1) (2 * M) q (Fin.snoc z 1 + unit (Fin.last d)) + 1 := by
      have hm : odoUnif (d + 1) (2 * M) (q - 1) (Fin.snoc z 1 + unit (Fin.last d)) ≤
          odoUnif (d + 1) (2 * M) q (Fin.snoc z 1 + unit (Fin.last d)) := hmono
      linarith [hm]
    rw [hgap]
    omega
  omega
