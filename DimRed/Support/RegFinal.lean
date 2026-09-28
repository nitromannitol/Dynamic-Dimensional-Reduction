import DimRed.Support.RegInduction
import DimRed.Support.RegSteps
import DimRed.Support.HCritical
import DimRed.Support.DimRedConcrete
open LatticeProb DimRed
namespace DimRed

/-- The joint induction with the dimensional-reduction step discharged. -/
theorem reg_induction_dimred
    (hconsist_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t → RegStrongFacet d M t → RegConsist d M t)
    (hweak_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t → RegStrongFacet d M t → RegWeak d M t)
    (hderiv_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t → RegStrongDeriv d M t)
    (hfacet_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t → RegStrongDeriv d M t → RegStrongFacet d M t)
    (htopple_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t → RegStrongFacet d M t → RegConsist d M t → RegTopple d M t) :
    ∀ d M t, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t :=
  reg_induction hconsist_step hweak_step hderiv_step hfacet_step htopple_step
    (fun d M t hd hM hprior => dimred_step_concrete d M t hd hM hprior)

end DimRed
