import DimRed.Support.StrongDerivRaw
import DimRed.Support.Stabilize
import DimRed.Support.RegBridges
open LatticeProb DimRed
namespace DimRed

/-- Strong facet compatibility at time `t` gives the one-step comparison
`v_t(z) ≤ v_{t+1}(z + unit k)` at a point `z` with a coordinate equal to one and
another at least two.  This is the paper's `v_t(y_i, 2, 1_j) ≥ v_{t-1}(y_i, 1, 1_j)`,
`dimred-corrected-arxiv.tex`. -/
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

/-- The facet point `(x + e_a, 1, 1_j)` lies in the positive orthant when
`x_a < M`. -/
theorem inPos_facetPoint_add_head {i j M : ℕ} (hM : 1 ≤ M) (x : Fin i → ℤ) (a : Fin i)
    (hx2 : ∀ a, 2 ≤ x a) (hxaM : x a < (M : ℤ))
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) :
    inPos (i + 1 + j) M (facetPoint (x + unit a) 1 j) := by
  intro l
  refine ⟨?_, ?_⟩
  · -- every coordinate is at least one
    by_cases hl : l = Fin.castAdd j (Fin.castSucc a)
    · rw [hl, facetPoint_head (x + unit a) 1 a, add_unit_self]
      have h0 := hx2 a
      omega
    · by_cases hhead : ∃ b : Fin i, l = Fin.castAdd j (Fin.castSucc b)
      · obtain ⟨b, rfl⟩ := hhead
        have hba : b ≠ a := by
          intro hcon
          exact hl (by rw [hcon])
        rw [facetPoint_head (x + unit a) 1 b, add_unit_other i x a b hba]
        have h0 := hx2 b
        omega
      · -- the mid or a tail coordinate: value `1`
        by_cases hmid : l = Fin.castAdd j (Fin.last i)
        · rw [hmid, facetPoint_mid]
        · -- a tail coordinate
          have htail : ∃ b : Fin j, l = Fin.natAdd (i + 1) b := by
            -- `l` is not a head coordinate and not the mid, so it is a tail
            have hlt : (l : ℕ) < i + 1 + j := l.isLt
            have hge : i + 1 ≤ (l : ℕ) := by
              by_contra hcon
              have hlt' : (l : ℕ) < i + 1 := by omega
              -- `l` is a head coordinate or the mid
              by_cases hlast : (l : ℕ) = i
              · exact hmid (Fin.ext (by rw [hlast]; simp [Fin.castAdd, Fin.last]))
              · -- `l` is a head coordinate, contradicting `hhead`
                exact hhead ⟨⟨(l : ℕ), by omega⟩, Fin.ext (by simp)⟩
            exact exists_natAdd_of_isTail l hge
          obtain ⟨b, rfl⟩ := htail
          rw [facetPoint_tail]
  · -- every coordinate is at most `M`
    by_cases hl : l = Fin.castAdd j (Fin.castSucc a)
    · rw [hl, facetPoint_head (x + unit a) 1 a, add_unit_self]
      omega
    · by_cases hhead : ∃ b : Fin i, l = Fin.castAdd j (Fin.castSucc b)
      · obtain ⟨b, rfl⟩ := hhead
        have hba : b ≠ a := by
          intro hcon
          exact hl (by rw [hcon])
        rw [facetPoint_head (x + unit a) 1 b, add_unit_other i x a b hba]
        have h0 := hx2 b
        have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
        have hbM : x b ≤ (M : ℤ) := by
          have h := (hxs.1 (Fin.castAdd j (Fin.castSucc b))).2
          rw [facetPoint_head x 1 b] at h
          exact h
        omega
      · by_cases hmid : l = Fin.castAdd j (Fin.last i)
        · rw [hmid, facetPoint_mid]
          have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
          omega
        · have htail : ∃ b : Fin j, l = Fin.natAdd (i + 1) b := by
            have hlt : (l : ℕ) < i + 1 + j := l.isLt
            have hge : i + 1 ≤ (l : ℕ) := by
              by_contra hcon
              have hlt' : (l : ℕ) < i + 1 := by omega
              by_cases hlast : (l : ℕ) = i
              · exact hmid (Fin.ext (by rw [hlast]; simp [Fin.castAdd, Fin.last]))
              · exact hhead ⟨⟨(l : ℕ), by omega⟩, Fin.ext (by simp)⟩
            exact exists_natAdd_of_isTail l hge
          obtain ⟨b, rfl⟩ := htail
          rw [facetPoint_tail]
          have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
          omega

theorem inPos_facetPoint_sub_head {i j M : ℕ} (hM : 1 ≤ M) (x : Fin i → ℤ) (a : Fin i)
    (hx2 : ∀ a, 2 ≤ x a) (hxa1 : 1 < x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) :
    inPos (i + 1 + j) M (facetPoint (x - unit a) 1 j) := by
  intro l
  refine ⟨?_, ?_⟩
  · -- every coordinate is at least one
    by_cases hl : l = Fin.castAdd j (Fin.castSucc a)
    · rw [hl, facetPoint_head (x - unit a) 1 a, sub_unit_self]
      have h0 := hx2 a
      omega
    · by_cases hhead : ∃ b : Fin i, l = Fin.castAdd j (Fin.castSucc b)
      · obtain ⟨b, rfl⟩ := hhead
        have hba : b ≠ a := by
          intro hcon
          exact hl (by rw [hcon])
        rw [facetPoint_head (x - unit a) 1 b, sub_unit_other i x a b hba]
        have h0 := hx2 b
        omega
      · -- the mid or a tail coordinate: value `1`
        by_cases hmid : l = Fin.castAdd j (Fin.last i)
        · rw [hmid, facetPoint_mid]
        · -- a tail coordinate
          have htail : ∃ b : Fin j, l = Fin.natAdd (i + 1) b := by
            -- `l` is not a head coordinate and not the mid, so it is a tail
            have hlt : (l : ℕ) < i + 1 + j := l.isLt
            have hge : i + 1 ≤ (l : ℕ) := by
              by_contra hcon
              have hlt' : (l : ℕ) < i + 1 := by omega
              -- `l` is a head coordinate or the mid
              by_cases hlast : (l : ℕ) = i
              · exact hmid (Fin.ext (by rw [hlast]; simp [Fin.castAdd, Fin.last]))
              · -- `l` is a head coordinate, contradicting `hhead`
                exact hhead ⟨⟨(l : ℕ), by omega⟩, Fin.ext (by simp)⟩
            exact exists_natAdd_of_isTail l hge
          obtain ⟨b, rfl⟩ := htail
          rw [facetPoint_tail]
  · -- every coordinate is at most `M`
    by_cases hl : l = Fin.castAdd j (Fin.castSucc a)
    · rw [hl, facetPoint_head (x - unit a) 1 a, sub_unit_self]
      have h := (hxs.1 (Fin.castAdd j (Fin.castSucc a))).2
      rw [facetPoint_head] at h
      omega
    · by_cases hhead : ∃ b : Fin i, l = Fin.castAdd j (Fin.castSucc b)
      · obtain ⟨b, rfl⟩ := hhead
        have hba : b ≠ a := by
          intro hcon
          exact hl (by rw [hcon])
        rw [facetPoint_head (x - unit a) 1 b, sub_unit_other i x a b hba]
        have h0 := hx2 b
        have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
        have hbM : x b ≤ (M : ℤ) := by
          have h := (hxs.1 (Fin.castAdd j (Fin.castSucc b))).2
          rw [facetPoint_head x 1 b] at h
          exact h
        omega
      · by_cases hmid : l = Fin.castAdd j (Fin.last i)
        · rw [hmid, facetPoint_mid]
          have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
          omega
        · have htail : ∃ b : Fin j, l = Fin.natAdd (i + 1) b := by
            have hlt : (l : ℕ) < i + 1 + j := l.isLt
            have hge : i + 1 ≤ (l : ℕ) := by
              by_contra hcon
              have hlt' : (l : ℕ) < i + 1 := by omega
              by_cases hlast : (l : ℕ) = i
              · exact hmid (Fin.ext (by rw [hlast]; simp [Fin.castAdd, Fin.last]))
              · exact hhead ⟨⟨(l : ℕ), by omega⟩, Fin.ext (by simp)⟩
            exact exists_natAdd_of_isTail l hge
          obtain ⟨b, rfl⟩ := htail
          rw [facetPoint_tail]
          have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
          omega

end DimRed
