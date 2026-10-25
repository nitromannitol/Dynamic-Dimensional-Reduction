module

public import DimRed.Support.RegFinal
public import DimRed.Support.WeakStep
public import DimRed.Support.StrongDerivStep

@[expose] public section

/-!
# The joint induction with the three open steps as hypotheses

`reg_all` closes the simultaneous induction for odometer regularity and dimensional reduction
(`dimred-corrected-arxiv.tex`, label `sec:dim_reduction`) modulo the three induction steps that are not yet proved: the
self-similarity step, the strong facet step and the strong topple step.  The weak facet step and
the strong derivative step are discharged by `weak_step_of_earlier` and `deriv_step_of_earlier`,
and the dimensional-reduction step by `reg_induction_dimred`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

/-- The self-similarity step: the clause `RegConsist` from the earlier triples, dimensional
reduction at the same triple, and strong facet compatibility at the same triple. -/
def ConsistStepHyp : Prop :=
  ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
    (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
    DimRedAt d M t → RegStrongFacet d M t → RegConsist d M t

/-- The strong facet step: the clause `RegStrongFacet` from the earlier triples, dimensional
reduction at the same triple, and the strong derivative clause at the same triple. -/
def FacetStepHyp : Prop :=
  ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
    (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
    DimRedAt d M t → RegStrongDeriv d M t → RegStrongFacet d M t

/-- The strong topple step: the clause `RegTopple` from the earlier triples, dimensional
reduction at the same triple, strong facet compatibility and self-similarity at the same
triple. -/
def ToppleStepHyp : Prop :=
  ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
    (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
    DimRedAt d M t → RegStrongFacet d M t → RegConsist d M t → RegTopple d M t

/-- The joint induction: all five regularity clauses and dimensional reduction, at every
dimension `d ≥ 1`, side `M ≥ 2` and time, from the three open induction steps. -/
theorem reg_all (hC : ConsistStepHyp) (hF : FacetStepHyp) (hT : ToppleStepHyp) :
    ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t :=
  reg_induction_dimred hC
    (fun d M t hd hM hprior _ hS => weak_step_of_earlier d M t hd hM hprior hS)
    (fun d M t hd hM hprior _ => deriv_step_of_earlier d M t hd hM hprior)
    hF hT

end DimRed
