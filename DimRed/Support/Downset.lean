/-
A down-set of `Fin d` of cardinality `i` is the initial segment of length `i`.
Used to identify the positions of the coordinates `≥ 2` in the sorting normal
form of a facet point.
-/
import DimRed.Support.StrongDerivPure

namespace DimRed

open LatticeProb

/-- A down-set of `Fin d` of cardinality `i` is the initial segment of length `i`. -/
theorem downset_eq_Iio (d i : ℕ) (hi : i < d) (T : Finset (Fin d))
    (hdown : ∀ b b' : Fin d, b ∈ T → b' ≤ b → b' ∈ T) (hcard : T.card = i) :
    T = Finset.Iio (⟨i, hi⟩ : Fin d) := by
  ext b
  simp only [Finset.mem_Iio]
  constructor
  · intro hb
    have hsub : Finset.Iic b ⊆ T := fun b' hb' => hdown b b' hb (Finset.mem_Iic.mp hb')
    have hle : (Finset.Iic b).card ≤ T.card := Finset.card_le_card hsub
    rw [Fin.card_Iic, hcard] at hle
    exact Fin.lt_def.mpr (by show (b : ℕ) < i; omega)
  · intro hb
    by_contra hbT
    have hsub : T ⊆ Finset.Iio b := by
      intro b' hb'
      rw [Finset.mem_Iio]
      by_contra hle
      exact hbT (hdown b' b hb' (le_of_not_gt hle))
    have hle : T.card ≤ (Finset.Iio b).card := Finset.card_le_card hsub
    rw [Fin.card_Iio, hcard] at hle
    have hbi : (b : ℕ) < i := Fin.lt_def.mp hb
    omega

end DimRed
