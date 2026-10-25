module

public import DimRed.Support.RegBridges
public import DimRed.Support.StrongDerivPure
public import DimRed.Support.Recursion
public import DimRed.Support.Stabilize

@[expose] public section
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
    (hS : RegStrongFacet d M (q - 1))
    (z : Site d) (hz : inSimplex d M z) (k : Fin d) (hk : z k = 1)
    (h2 : ∃ l, 2 ≤ z l)
    (hgap : odoUnif d (2 * M) q z = odoUnif d (2 * M) q (z + unit k) + 1) :
    odoUnif d (2 * M) q z = odoUnif d (2 * M) (q - 1) z + 1 := by
  -- the first-difference bound at `q - 1`
  have hfd := odo_first_diff d M (by omega) (by omega) (q - 1) k z (by rw [hk])
  -- the one-step bound at `q`
  have hstep := (odo_succ_sub_bounds d (2 * M)
    (fun _ => 2 * (d : ℤ)) (q - 1) z).2
  rw [show q - 1 + 1 = q by omega] at hstep
  -- the head is at most the neighbour at `q - 1`
  have hprev_le : odoUnif d (2 * M) (q - 1) z ≤
      odoUnif d (2 * M) (q - 1) (z + unit k) := by
    by_cases hg : odoUnif d (2 * M) (q - 1) z =
        odoUnif d (2 * M) (q - 1) (z + unit k) + 1
    · -- the gap at `q - 1` would force the head to stay and the neighbour to
      -- rise at `q`, contradicting the gap at `q`
      have htopple := strong_facet_step_topple_of_reg d M (q - 1) hS
      have hres := (htopple z k hz hk h2 hg).1
      rw [show q - 1 + 1 = q by omega] at hres
      have hmid := (htopple z k hz hk h2 hg).2
      rw [show q - 1 + 1 = q by omega] at hmid
      omega
    · -- otherwise the first-difference bound gives it
      omega
  -- monotonicity in time at the neighbour
  have hmono := odo_mono d (2 * M) (fun _ => 2 * (d : ℤ))
    (show q - 1 ≤ q by omega) (z + unit k)
  -- the gap at `q` and the one-step bound at `q`
  have hstep' : odoUnif d (2 * M) q z ≤
      odoUnif d (2 * M) (q - 1) z + 1 := by
    have h := hstep
    simp only [odoUnif] at h ⊢
    omega
  have hchain : odoUnif d (2 * M) (q - 1) z + 1 ≤
      odoUnif d (2 * M) q z := by
    have h1 : odoUnif d (2 * M) (q - 1) z + 1 ≤
        odoUnif d (2 * M) (q - 1) (z + unit k) + 1 := by omega
    have h2 : odoUnif d (2 * M) (q - 1) (z + unit k) + 1 ≤
        odoUnif d (2 * M) q (z + unit k) + 1 := by
      have hm : odoUnif d (2 * M) (q - 1) (z + unit k) ≤
          odoUnif d (2 * M) q (z + unit k) := hmono
      linarith
    rw [hgap]
    omega
  omega

end DimRed
