import DimRed.Support.OneDimConsistAll
import DimRed.Support.StrongDerivStep

open LatticeProb DimRed

namespace DimRed

/-- The time bound feeding `hprev` of `odo_one_consist_all`: a time below the
topple time of scale `j` is below the topple time of every larger scale. -/
theorem toppleTime_le_of_lt_of_le {j K M t t' : ℕ}
    (hmono : ∀ {a b : ℕ}, j ≤ a → a ≤ b → b < M → toppleTime 1 a ≤ toppleTime 1 b)
    (hjK : j < K) (hKM : K ≤ M) (hK2 : 2 ≤ K)
    (ht : (t : ℕ∞) ≤ toppleTime 1 j) (htt : t' < t) :
    (t' : ℕ∞) ≤ toppleTime 1 (K - 1) := by

  have h1 : (t' : ℕ∞) < (t : ℕ∞) := by exact_mod_cast htt
  have hjK1 : j ≤ K - 1 := by omega
  have hK1M : K - 1 < M := by omega
  have h2 : (t : ℕ∞) ≤ toppleTime 1 (K - 1) :=
    le_trans ht (hmono (a := j) (b := K - 1) le_rfl hjK1 hK1M)
  exact le_of_lt (lt_of_lt_of_le h1 h2)


/-- The `hfacet` regime of `odo_one_consist_all`: the hypothesis
`(s+1 : ℕ∞) < toppleTime 1 (K-1)` puts `s` below the topple time of scale `K`. -/
theorem toppleTime_lt_of_succ_lt {K M s : ℕ} (hKM : K < M) (hK2 : 2 ≤ K)
    (hmono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → b < M → toppleTime 1 a ≤ toppleTime 1 b)
    (h : ((s + 1 : ℕ) : ℕ∞) < toppleTime 1 (K - 1)) :
    (s : ℕ∞) < toppleTime 1 K := by

  have hK1 : 1 ≤ K - 1 := by omega
  have hK1K : K - 1 ≤ K := by omega
  have h1 : ((s + 1 : ℕ) : ℕ∞) ≤ toppleTime 1 K :=
    le_trans (le_of_lt h) (hmono (a := K - 1) (b := K) hK1 hK1K hKM)
  have h2 : (s : ℕ∞) < ((s + 1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_lt]
    omega
  exact lt_of_lt_of_le h2 h1


/-- The topple time of the scale-one cube is one. -/
theorem toppleTime_one_one : toppleTime 1 1 = 1 := by
  apply le_antisymm
  · rw [toppleTime_eq_corner 1 1 (by norm_num) (by omega)]
    apply sInf_le
    exact ⟨1, ⟨by norm_num, corner_one_le 1⟩, rfl⟩
  · exact one_le_toppleTime 1 1

/-- The facet point with an empty head is the constant vector with the middle
coordinate replaced by `c`. -/
theorem facetPoint_zero_head' (c c' : ℤ) (j : ℕ) :
    facetPoint (fun _ : Fin 0 => c') c j
      = fun k : Fin (0 + 1 + j) =>
          if k = (⟨0, by omega⟩ : Fin (0 + 1 + j)) then c else 1 := by
  have h : (fun _ : Fin 0 => c') = (fun _ : Fin 0 => (0 : ℤ)) := by
    funext a
    exact absurd a.2 (by omega)
  rw [h, facetPoint_zero_head]

end DimRed
