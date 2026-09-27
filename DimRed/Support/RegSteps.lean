/-
The steps of the joint induction of `dimred.tex:1117-1128` that are complete,
each stated as its own theorem so that the induction of
`DimRed.Support.RegInduction` can be applied.

`deriv_step_of_earlier` is the strong derivative clause: the branch `1 ≤ i` is
`strong_deriv_pos_head` fed by the pure second difference `odo_pure_diff`, and
the branch `i = 0` is the early-time Case 1 `strong_deriv_zero_head`.

`weak_step_of_earlier` is the weak facet clause, which the paper proves from
strong facet compatibility at the same triple (`dimred.tex:1436-1445`); it
therefore consumes `RegStrongFacet d M t` as an argument rather than deriving it.

The remaining steps (`facet_step`, `topple_step`, `dimred_step`, `consist_step`)
are not yet written; see the run's STATUS file.
-/
import DimRed.Support.RegBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The strong derivative clause of Proposition 4.1 at one triple. -/
theorem deriv_step (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (_hred : DimRedAt d M t) :
    RegStrongDeriv d M t :=
  deriv_step_of_earlier d M t hd hM hprior

/-- The weak facet compatibility clause of Proposition 4.1 at one triple, from
strong facet compatibility at the same triple. -/
theorem weak_step (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (_hred : DimRedAt d M t) (hfacet : RegStrongFacet d M t) :
    RegWeak d M t :=
  weak_step_of_earlier d M t hd hM hprior hfacet

end DimRed
