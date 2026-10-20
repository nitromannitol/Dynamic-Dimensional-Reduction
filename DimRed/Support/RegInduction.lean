/-
The simultaneous induction bookkeeping for odometer regularity and dimensional
reduction, `dimred-corrected-arxiv.tex`, label `sec:dim_reduction`.  The six predicates below are the five
time-slice clauses of Proposition 4.1 together with the reduction identity.
The transition predicates in `DimRed.Support.DimRedStep` are reused by the
arguments which discharge the six induction-step hypotheses; they are not
duplicated here.
-/
import DimRed.Support.DimRedStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

/-- A triple is earlier in the dimension-side-time order of the section labelled `sec:dim_reduction` in `dimred-corrected-arxiv.tex`. -/
def regEarlier (d M t d' M' t' : ℕ) : Prop :=
  d' < d ∨ d' = d ∧ M' < M ∨ d' = d ∧ M' = M ∧ t' < t

/-- The self-similarity clause at one dimension, side, and time. -/
def RegConsist (d M t : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ M → (t : ℕ∞) ≤ toppleTime d j →
    ∀ x : Site d, inSimplex d M x →
      (∀ i : Fin d, (M : ℤ) - (j : ℤ) < x i) →
      odoUnif d (2 * M) t x =
        odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ)))

/-- Weak facet compatibility at one dimension, side, and time. -/
def RegWeak (d M t : ℕ) : Prop :=
  ∀ i j : ℕ, i + 1 + j = d → 1 ≤ t →
    ∀ x : Fin i → ℤ, (∀ a, 2 ≤ x a) →
      inSimplex (i + 1 + j) M (facetPoint x 1 j) →
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) =
          odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 →
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) =
        odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)

/-- Strong derivative compatibility at one dimension, side, and time. -/
def RegStrongDeriv (d M t : ℕ) : Prop :=
  ∀ i j : ℕ, i + 1 + j = d →
    ∀ x : Fin i → ℤ, (∀ a, 2 ≤ x a) →
      inSimplex (i + 1 + j) M (facetPoint x 1 j) →
      ((t : ℕ∞) < toppleTime (i + 1 + j) M ∨
        (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) →
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) -
          odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2

/-- Strong facet compatibility at one dimension, side, and time. -/
def RegStrongFacet (d M t : ℕ) : Prop :=
  ∀ i j : ℕ, i + 1 + j = d →
    ∀ x : Fin i → ℤ, (∀ a, 2 ≤ x a) →
      inSimplex (i + 1 + j) M (facetPoint x 1 j) →
      ((t : ℕ∞) < toppleTime (i + 1 + j) M ∨
        (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) →
      odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) =
          odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 →
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j) =
          odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) ∧
        odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j) =
          odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1

/-- Strong topple control at one dimension, side, and time. -/
def RegTopple (d M t : ℕ) : Prop :=
  (toppleTime d (M - 1) ≤ (t : ℕ∞)) →
    simplexMax d M (fun x =>
      odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1

/-- Dimensional reduction at one dimension, side, and time: the odometer in dimension `d`
on the centre slice of the last coordinate agrees with the odometer in dimension `d - 1`.

The larger dimension is the index.  Indexing by the smaller one instead would put the
statement out of reach of the induction: proving the reduction from `d + 1` down to `d` needs
regularity in dimension `d + 1` at earlier times, and `d + 1` is not earlier than `d` in the
order of the section labelled `sec:dim_reduction` in `dimred-corrected-arxiv.tex`. -/
def DimRedAt (d M t : ℕ) : Prop :=
  ∀ e : ℕ, 1 ≤ e → d = e + 1 → ∀ x : Site e, inSimplex e M x →
    odoUnif (e + 1) (2 * M) t (Fin.snoc x 1) = odoUnif e (2 * M) t x

/-- The five regularity clauses at one dimension, side, and time. -/
def Reg (d M t : ℕ) : Prop :=
  RegConsist d M t ∧ RegWeak d M t ∧ RegStrongDeriv d M t ∧
    RegStrongFacet d M t ∧ RegTopple d M t

theorem reg_induction
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
        DimRedAt d M t → RegStrongFacet d M t → RegConsist d M t → RegTopple d M t)
    (hdimred_step :
      ∀ d M t : ℕ, 1 ≤ d → 2 ≤ M →
        (∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
          1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') →
        DimRedAt d M t) :
    ∀ d M t, 1 ≤ d → 2 ≤ M → Reg d M t ∧ DimRedAt d M t := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ihM =>
      intro t
      induction t using Nat.strong_induction_on with
      | _ t iht =>
        intro hd hM
        have hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
            1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t' := by
          intro d' M' t' he hd' hM'
          rcases he with hdlt | hside | htime
          · exact ihd d' hdlt M' t' hd' hM'
          · rcases hside with ⟨hdeq, hMlt⟩
            subst hdeq
            exact ihM M' hMlt t' hd hM'
          · rcases htime with ⟨hdeq, hMeq, htlt⟩
            subst hdeq
            subst hMeq
            exact iht t' htlt hd hM
        have hdimred := hdimred_step d M t hd hM hprior
        have hderiv := hderiv_step d M t hd hM hprior hdimred
        have hfacet := hfacet_step d M t hd hM hprior hdimred hderiv
        have hweak := hweak_step d M t hd hM hprior hdimred hfacet
        have hconsist := hconsist_step d M t hd hM hprior hdimred hfacet
        have htopple := htopple_step d M t hd hM hprior hdimred hfacet hconsist
        exact ⟨⟨hconsist, hweak, hderiv, hfacet, htopple⟩, hdimred⟩

end DimRed
