module

public import DimRed.Support.RegInduction
public import DimRed.Support.RegSteps
public import DimRed.Support.HCritical

@[expose] public section
open LatticeProb DimRed
namespace DimRed

/-- The concrete dimensional-reduction step: `dimred_step_of_earlier` with its
`hcritical` hypothesis discharged by `hcritical_from_prior`.

At `t < 2` both odometers are `1` at every site of the cube from the first step
(`odoUnif_one_eq_one`), so reduction holds; at `t ≥ 2` the critical case is
`hcritical_from_prior`.  This is the `hdimred_step` argument of `reg_induction`. -/
theorem dimred_step_concrete (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    DimRedAt d M t := by
  rcases Nat.lt_or_ge t 2 with ht | ht2
  · -- `t < 2`: the odometer is `1` at every site from the first step
    intro e he hde x hx
    subst hde
    rcases Nat.eq_zero_or_pos t with rfl | ht1
    · simp only [odoUnif, odo]
    · have ht1' : t = 1 := by omega
      subst ht1'
      rw [odoUnif_one_eq_one (e + 1) M (Fin.snoc x 1)
            (inSimplex_inCube (e + 1) M (Fin.snoc x 1)
              (inSimplex_snoc_one_local x hx (by omega))),
          odoUnif_one_eq_one e M x (inSimplex_inCube e M x hx)]
  · refine dimred_step_of_earlier d M t hd hM hprior ?_
    intro e q he hde hqt z hz hz1 hgap hred hweak hstrong htopple hconsist
    have htq : q + 1 = t := by omega
    rw [htq]
    exact hcritical_from_prior d M t hd hM (by omega)
      (fun d' M' t' he' hd' hM' => hprior d' M' t' (by
        rcases he' with hlt | ⟨rfl, hlt⟩ | ⟨rfl, rfl, hlt⟩
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl, by omega⟩)) hd' hM')
      e he hde z hz hz1 (by rw [← hqt]; exact hgap)
      (by rw [← hqt]; exact hred) (by rw [← hqt]; exact hweak)
      (by rw [← hqt]; exact hstrong)
      (by
        intro i hi hie hle
        have h := htopple i hi hie (by rw [hqt]; exact hle)
        rw [hqt] at h
        have h1 : t - 1 + 1 = t := by omega
        have h2 : t - 1 - 1 = t - 2 := by omega
        rw [h1, h2] at h
        exact h)
      (by rw [← hqt]; exact hconsist)

end DimRed
