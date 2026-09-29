import DimRed.Support.StrongDerivRaw
import DimRed.Support.Stabilize
import DimRed.Support.RegBridges
open LatticeProb DimRed
namespace DimRed

/-- Strong facet compatibility at time `t` gives the one-step comparison
`v_t(z) ≤ v_{t+1}(z + unit k)` at a point `z` with a coordinate equal to one and
another at least two.  This is the paper's `v_t(y_i, 2, 1_j) ≥ v_{t-1}(y_i, 1, 1_j)`,
`dimred.tex:1345-1348`. -/
theorem strong_raw_le (d M t : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (hS : RegStrongFacet d M t)
    (z : Site d) (hz : inPos d M z) (k : Fin d) (hk : z k = 1) (h2 : ∃ l, 2 ≤ z l) :
    odoUnif d (2 * M) t z ≤ odoUnif d (2 * M) (t + 1) (z + unit k) := by
  by_cases hgap : odoUnif d (2 * M) t z = odoUnif d (2 * M) t (z + unit k) + 1
  · -- the gap: the head stays and the neighbour rises, so they meet
    have hrise := strong_raw d M t hS z hz k hk h2 hgap
    rw [hrise]
    linarith
  · -- no gap: the first-difference bound gives `v_t(z) ≤ v_t(z + unit k)`
    have hfd := odo_first_diff d M hd hM t k z (by rw [hk])
    rw [hk] at hfd
    have hmono : odoUnif d (2 * M) t (z + unit k) ≤ odoUnif d (2 * M) (t + 1) (z + unit k) :=
      odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (Nat.le_succ t) (z + unit k)
    -- `v_t(z) - v_t(z+e_k) ≤ 1` and the difference is an integer, so if it is
    -- not `1` it is `≤ 0`
    have hstep := (odo_succ_sub_bounds d (2 * M) (fun _ => 2 * (d : ℤ)) t z).2
    -- `v_t(z) - v_t(z+e_k) ≤ 1` and it is not `1`, so it is `≤ 0`
    have hle0 : odoUnif d (2 * M) t z ≤ odoUnif d (2 * M) t (z + unit k) := by
      by_contra hcon
      have hcon' : odoUnif d (2 * M) t (z + unit k) < odoUnif d (2 * M) t z := not_le.mp hcon
      have : odoUnif d (2 * M) t z = odoUnif d (2 * M) t (z + unit k) + 1 := by omega
      exact hgap this
    linarith

end DimRed
