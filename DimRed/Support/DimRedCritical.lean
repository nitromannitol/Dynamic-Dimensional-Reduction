/-
The unit-gap interior branch of dimensional reduction, `dimred-corrected-arxiv.tex:981-1008`, which is the
one branch `DimRed/Support/DimRedStep.lean` leaves open.  The point has every coordinate above
one, so the least index with a tail of ones is the last, and the facet gap at the previous time
is exactly one.  The paper splits on whether the previous-but-one time has reached the topple
time of the smaller cube: at or after it, strong topple control freezes both odometers and the
reduction carries forward; below it, self-similarity forces the two innermost layers of the
last coordinate to agree, which contradicts the gap.
-/
import DimRed.Support.DimRedStep
import DimRed.Support.SnocSimplex
import DimRed.Support.ToppleTime

namespace DimRed

open LatticeProb

/-- Strong topple control freezes a site that has just fired: if the odometer rose by one
between `t-2` and `t-1`, and no site rises by two between `t-2` and `t`, then it does not
rise again at `t`.  the section titled `Dimensional reduction` in `dimred-corrected-arxiv.tex`. -/
theorem odo_frozen_of_topple (d M t : ℕ) (_hd : 1 ≤ d) (_hM : 2 ≤ M) (_ht : 2 ≤ t)
    (z : Site d) (hz : inSimplex d M z)
    (hjump : odoUnif d (2 * M) (t - 1) z = odoUnif d (2 * M) (t - 2) z + 1)
    (htopple : simplexMax d M
        (fun w => odoUnif d (2 * M) t w - odoUnif d (2 * M) (t - 2) w) ≤ 1) :
    odoUnif d (2 * M) t z = odoUnif d (2 * M) (t - 1) z := by
  have hle : odoUnif d (2 * M) t z ≤ odoUnif d (2 * M) (t - 1) z := by
    have hmax := le_simplexMax d M
      (fun w => odoUnif d (2 * M) t w - odoUnif d (2 * M) (t - 2) w) z hz
    have hsub : odoUnif d (2 * M) t z - odoUnif d (2 * M) (t - 2) z ≤ 1 := by
      linarith
    have : odoUnif d (2 * M) t z ≤ odoUnif d (2 * M) (t - 2) z + 1 := by omega
    rw [← hjump] at this
    exact this
  have hge : odoUnif d (2 * M) (t - 1) z ≤ odoUnif d (2 * M) t z := by
    have hmono : t - 1 ≤ t := by omega
    exact odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) hmono z
  omega

/-- The reflecting boundary identity `eq:reflecting_boundaries`, `dimred-corrected-arxiv.tex:997-1006`.
Below the topple time, self-similarity at scale `M` and dimensional reduction at both scales
identify the layer `2` of the last coordinate with the layer `1`. -/
theorem odo_reflecting_boundary (d M t : ℕ) (_hd : 1 ≤ d) (_hM : 2 ≤ M)
    (z : Site d) (_hz : inSimplex d M z) (_hz1 : ∀ k, 1 < z k)
    (hself : odoUnif (d + 1) (2 * M) t (Fin.snoc z 2)
        = odoUnif (d + 1) (2 * (M - 1)) t (Fin.snoc (fun k => z k - 1) 1))
    (hredM1 : odoUnif (d + 1) (2 * (M - 1)) t (Fin.snoc (fun k => z k - 1) 1)
        = odoUnif d (2 * (M - 1)) t (fun k => z k - 1))
    (hredM : odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) = odoUnif d (2 * M) t z)
    (hconsist : odoUnif d (2 * M) t z = odoUnif d (2 * (M - 1)) t (fun k => z k - 1)) :
    odoUnif (d + 1) (2 * M) t (Fin.snoc z 2)
      = odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) := by
  calc
    odoUnif (d + 1) (2 * M) t (Fin.snoc z 2)
        = odoUnif (d + 1) (2 * (M - 1)) t (Fin.snoc (fun k => z k - 1) 1) := hself
    _ = odoUnif d (2 * (M - 1)) t (fun k => z k - 1) := hredM1
    _ = odoUnif d (2 * M) t z := hconsist.symm
    _ = odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) := hredM.symm

/-- The unit-gap interior branch of dimensional reduction, `dimred-corrected-arxiv.tex:981-1008`, which is
the one branch `DimRed.Support.DimRedStep.odo_dimred_step` leaves open.  The point has every
coordinate above one, so the least index with a tail of ones is `i = d`, and the facet gap at
time `t-1` is exactly one.  The paper splits on whether `t-2` has reached the topple time of
the smaller cube. -/
theorem odo_dimred_critical (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (ht : 2 ≤ t)
    (z : Site d) (hz : inSimplex d M z) (hz1 : ∀ k, 1 < z k)
    -- dimensional reduction at the two previous times, both scales
    (hprev : ∀ (s : ℕ) (m : ℕ), s < t → 2 ≤ m → m ≤ M → ∀ y : Site d, inSimplex d m y →
      odoUnif (d + 1) (2 * m) s (Fin.snoc y 1) = odoUnif d (2 * m) s y)
    -- the smallest scale, where both odometers are `1` from the first step
    (hprev_one : ∀ (s : ℕ), s < t → ∀ y : Site d, inSimplex d 1 y →
      odoUnif (d + 1) 2 s (Fin.snoc y 1) = odoUnif d 2 s y)
    -- strong facet compatibility in dimension d+1 from (t-2) to (t-1), in the
    -- form the clause of Proposition 4.1 supplies: the point `Fin.snoc z 1` has
    -- a coordinate equal to one, and its neighbour in that direction is
    -- `Fin.snoc z 2`
    (hgap : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1)
        = odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 2) + 1)
    (hjump : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1)
        = odoUnif (d + 1) (2 * M) (t - 2) (Fin.snoc z 1) + 1)
    -- strong topple control in both dimensions, valid once (t-2) has reached the topple time
    (htopple_up : toppleTime (d + 1) (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞) →
      simplexMax (d + 1) M (fun w => odoUnif (d + 1) (2 * M) t w
        - odoUnif (d + 1) (2 * M) (t - 2) w) ≤ 1)
    (htopple_down : toppleTime (d + 1) (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞) →
      simplexMax d M (fun w => odoUnif d (2 * M) t w - odoUnif d (2 * M) (t - 2) w) ≤ 1)
    -- self-similarity at scale M, below the topple time
    (hconsist : ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (d + 1) (M - 1) →
      odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 2)
        = odoUnif (d + 1) (2 * (M - 1)) (t - 1) (Fin.snoc (fun k => z k - 1) 1) ∧
      odoUnif d (2 * M) (t - 1) z = odoUnif d (2 * (M - 1)) (t - 1) (fun k => z k - 1)) :
    odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) = odoUnif d (2 * M) t z := by
  by_cases htopple_le : toppleTime (d + 1) (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞)
  · -- late branch: toppleTime ≤ t-2, use strong topple to freeze both odometers
    have hlate_up : simplexMax (d + 1) M
        (fun w => odoUnif (d + 1) (2 * M) t w
          - odoUnif (d + 1) (2 * M) (t - 2) w) ≤ 1 := htopple_up htopple_le
    have hlate_down : simplexMax d M
        (fun w => odoUnif d (2 * M) t w - odoUnif d (2 * M) (t - 2) w) ≤ 1 :=
      htopple_down htopple_le
    have hX : inSimplex (d + 1) M (Fin.snoc z 1) :=
      inSimplex_snoc_one_local z hz (by omega)
    have hjump_up : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) =
        odoUnif (d + 1) (2 * M) (t - 2) (Fin.snoc z 1) + 1 := hjump
    have hfreeze_up : odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) =
        odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) :=
      odo_frozen_of_topple (d + 1) M t (by omega) hM ht (Fin.snoc z 1) hX hjump_up hlate_up
    have hprev_t1 : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) =
        odoUnif d (2 * M) (t - 1) z :=
      hprev (t - 1) M (by omega) (by omega) (by omega) z hz
    have hprev_t2 : odoUnif (d + 1) (2 * M) (t - 2) (Fin.snoc z 1) =
        odoUnif d (2 * M) (t - 2) z :=
      hprev (t - 2) M (by omega) (by omega) (by omega) z hz
    have hjump_down : odoUnif d (2 * M) (t - 1) z =
        odoUnif d (2 * M) (t - 2) z + 1 := by
      rw [← hprev_t1, hjump_up, hprev_t2]
    have hfreeze_down : odoUnif d (2 * M) t z =
        odoUnif d (2 * M) (t - 1) z :=
      odo_frozen_of_topple d M t hd hM ht z hz hjump_down hlate_down
    calc
      odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) =
          odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) := hfreeze_up
      _ = odoUnif d (2 * M) (t - 1) z := hprev_t1
      _ = odoUnif d (2 * M) t z := hfreeze_down.symm
  · -- early branch: t-2 < toppleTime, derive contradiction via reflecting boundary
    have h_lt : ((t - 2 : ℕ) : ℕ∞) < toppleTime (d + 1) (M - 1) :=
      lt_of_not_ge htopple_le
    have h_le : ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (d + 1) (M - 1) := by
      by_cases htop : toppleTime (d + 1) (M - 1) = ⊤
      · rw [htop]; exact le_top
      · have h_fin : ∃ n : ℕ, toppleTime (d + 1) (M - 1) = (n : ℕ∞) := by
          refine ⟨(toppleTime (d + 1) (M - 1)).toNat,
            (ENat.coe_toNat htop).symm⟩
        rcases h_fin with ⟨n, hn⟩
        rw [hn] at h_lt ⊢
        have h_lt_nat : (t - 2 : ℕ) < n := by
          exact (Nat.cast_lt (α := ℕ∞)).mp h_lt
        have h_le_nat : (t - 1 : ℕ) ≤ n := by omega
        exact (Nat.cast_le (α := ℕ∞)).mpr h_le_nat
    have h_cons := hconsist h_le
    rcases h_cons with ⟨h_self, h_red⟩
    have hz_sub : inSimplex d (M - 1) (fun k => z k - 1) := by
      rcases hz with ⟨hz_bounds, hz_order⟩
      have hz_sub_bounds : ∀ i : Fin d, (1 : ℤ) ≤ (fun k => z k - 1) i ∧ (fun k => z k - 1) i ≤ ((M - 1 : ℕ) : ℤ) := by
        intro i
        have hbound := hz_bounds i
        rcases hbound with ⟨hlo, hhi⟩
        have htwo_nat : 2 ≤ z i := by
          have := hz1 i
          omega
        have htwo : (2 : ℤ) ≤ (z i : ℤ) := by exact_mod_cast htwo_nat
        have hlo' : (1 : ℤ) ≤ (z i : ℤ) - 1 := by linarith
        have hhi' : (z i : ℤ) - 1 ≤ ((M - 1 : ℕ) : ℤ) := by
          have hM1 : 1 ≤ M := by omega
          rw [Nat.cast_sub hM1, Nat.cast_one]
          linarith
        exact ⟨hlo', hhi'⟩
      have hz_sub_order : ∀ i j : Fin d, i ≤ j → (fun k => z k - 1) j ≤ (fun k => z k - 1) i := by
        intro i j hij
        have h := hz_order i j hij
        linarith
      exact ⟨hz_sub_bounds, hz_sub_order⟩
    have hredM : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) = odoUnif d (2 * M) (t - 1) z :=
      hprev (t - 1) M (by omega) (by omega) (by omega) z hz
    have hredM1 : odoUnif (d + 1) (2 * (M - 1)) (t - 1) (Fin.snoc (fun k => z k - 1) 1) =
        odoUnif d (2 * (M - 1)) (t - 1) (fun k => z k - 1) :=
      (by
        by_cases hM3 : 3 ≤ M
        · exact hprev (t - 1) (M - 1) (by omega) (by omega) (by omega)
            (fun k => z k - 1) hz_sub
        · have hM2 : M = 2 := by omega
          subst hM2
          exact hprev_one (t - 1) (by omega) (fun k => z k - 1) hz_sub)
    have h_eq : odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 2) =
        odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) := by
      calc
        odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 2) =
            odoUnif (d + 1) (2 * (M - 1)) (t - 1)
              (Fin.snoc (fun k => z k - 1) 1) := h_self
        _ = odoUnif d (2 * (M - 1)) (t - 1) (fun k => z k - 1) := hredM1
        _ = odoUnif d (2 * M) (t - 1) z := h_red.symm
        _ = odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) := hredM.symm
    rw [h_eq] at hgap
    omega

end DimRed
