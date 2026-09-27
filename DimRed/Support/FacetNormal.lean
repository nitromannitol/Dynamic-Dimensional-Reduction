/-
The sorting normal form of a point of the positive orthant with a coordinate
equal to `1`: after sorting the coordinates with that coordinate first among the
ones, the point is `facetPoint z 1 j` and its neighbour in that direction is
`facetPoint z 2 j`.  This is the normal form that weak and strong facet
compatibility are stated for.
-/
import DimRed.Support.StrongDerivPure
import DimRed.Support.Downset
import DimRed.Support.FacetNbr
import DimRed.Support.Symmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb


theorem facetPoint_antitone (i j : ℕ) (z : Fin i → ℤ) (hanti : Antitone z) (hz : ∀ a, 2 ≤ z a) :
    ∀ l m : Fin (i + 1 + j), l ≤ m → facetPoint z 1 j m ≤ facetPoint z 1 j l := by
  intro l m hlm
  have hle : (l : ℕ) ≤ (m : ℕ) := hlm
  have key : ∀ p q : Fin (i + 1 + j), (p : ℕ) ≤ (q : ℕ) →
      facetPoint z 1 j q ≤ facetPoint z 1 j p := by
    intro p q hpq
    by_cases hp : (p : ℕ) < i
    · by_cases hq : (q : ℕ) < i
      · have h1 : (⟨(p : ℕ), hp⟩ : Fin i) ≤ ⟨(q : ℕ), hq⟩ := by
          rw [Fin.le_def]; simp only; exact hpq
        have e1 : facetPoint z 1 j p = z ⟨(p : ℕ), hp⟩ := by
          have hpp : p = Fin.castAdd j (Fin.castSucc ⟨(p : ℕ), hp⟩) := Fin.ext rfl
          conv_lhs => rw [hpp]
          rw [facetPoint_head]
        have e2 : facetPoint z 1 j q = z ⟨(q : ℕ), hq⟩ := by
          have hqq : q = Fin.castAdd j (Fin.castSucc ⟨(q : ℕ), hq⟩) := Fin.ext rfl
          conv_lhs => rw [hqq]
          rw [facetPoint_head]
        rw [e1, e2]
        exact hanti h1
      · have hqi : i ≤ (q : ℕ) := le_of_not_gt hq
        have e1 : facetPoint z 1 j p = z ⟨(p : ℕ), hp⟩ := by
          have hpp : p = Fin.castAdd j (Fin.castSucc ⟨(p : ℕ), hp⟩) := Fin.ext rfl
          conv_lhs => rw [hpp]
          rw [facetPoint_head]
        have e2 : facetPoint z 1 j q = 1 := by
          rcases lt_or_eq_of_le hqi with hlt | heq
          · have hqq : q = Fin.natAdd (i + 1) ⟨(q : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
              simp only [Fin.val_natAdd]; omega)
            conv_lhs => rw [hqq]
            rw [facetPoint_tail]
          · have hqq : q = Fin.castAdd j (Fin.last i) := Fin.ext (by
              simp only [Fin.val_castAdd, Fin.val_last]
              omega)
            conv_lhs => rw [hqq]
            rw [facetPoint_mid]
        rw [e1, e2]
        linarith [hz ⟨(p : ℕ), hp⟩]
    · have hpi : i ≤ (p : ℕ) := le_of_not_gt hp
      have hqi : i ≤ (q : ℕ) := le_trans hpi hpq
      have e2 : facetPoint z 1 j q = 1 := by
        rcases lt_or_eq_of_le hqi with hlt | heq
        · have hqq : q = Fin.natAdd (i + 1) ⟨(q : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
            simp only [Fin.val_natAdd]; omega)
          conv_lhs => rw [hqq]
          rw [facetPoint_tail]
        · have hqq : q = Fin.castAdd j (Fin.last i) := Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_last]
            omega)
          conv_lhs => rw [hqq]
          rw [facetPoint_mid]
      have e1 : facetPoint z 1 j p = 1 := by
        rcases lt_or_eq_of_le hpi with hlt | heq
        · have hpp : p = Fin.natAdd (i + 1) ⟨(p : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
            simp only [Fin.val_natAdd]; omega)
          conv_lhs => rw [hpp]
          rw [facetPoint_tail]
        · have hpp : p = Fin.castAdd j (Fin.last i) := Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_last]
            omega)
          conv_lhs => rw [hpp]
          rw [facetPoint_mid]
      rw [e1, e2]
  exact key l m hle

end DimRed
