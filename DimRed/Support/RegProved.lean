/-
The joint induction of `dimred-corrected-arxiv.tex`, label `sec:dim_reduction` with all six step hypotheses discharged:
odometer regularity (Proposition 4.1) and dimensional reduction hold at every dimension
`d ≥ 1`, half-side `M ≥ 2` and time `t`.  The ten frozen statements of Theorem 1.1,
Corollary 1.1 and Proposition 4.1 are read off from `reg_proved` by the bridges of
`DimRed.Support.FrozenFromReg` and `DimRed.Support.FrozenFromRegMain`, which this module
re-exports for them.
-/
import DimRed.Support.RegAll
import DimRed.Support.ConsistStepFinal
import DimRed.Support.FacetStepFinal
import DimRed.Support.ToppleStepFinal
import DimRed.Support.FrozenFromReg
import DimRed.Support.FrozenFromRegMain

set_option autoImplicit false

namespace DimRed

/-- Proposition 4.1 and dimensional reduction, jointly, at every dimension, side and time. -/
theorem reg_proved : ∀ d M t, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t :=
  reg_all consist_step_of_earlier facet_step_of_earlier topple_step_of_earlier

end DimRed
