import DimRed.Support.StrongDerivStep
import DimRed.Support.DimRedCritical
import DimRed.Support.ToppleGeneral
import DimRed.Support.OneDimConsistAll
import DimRed.Support.SelfSimilarityMain
import DimRed.Support.CornerReaches
import DimRed.Support.WeakStep

/-!
# Bridges from the regularity clauses to the step predicates

The bridges from the time-slice clauses of Proposition 4.1 to the step predicates
of `DimRed.Support.DimRedStep`.

`weak_facet_step` and `strong_facet_step` are stated at raw points of the sorted
domain; the clauses of Proposition 4.1 are stated at facet points.  The sorting
normal form `facet_normal_form` carries one to the other, which is what
`weak_raw` and `strong_raw` do.  The first conjunct of `strong_facet_step` is the
first-difference bound at a coordinate equal to one, which is Corollary 2.2.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The first conjunct of strong facet compatibility at a raw point: the site
with a coordinate equal to one does not topple. -/
theorem strong_raw_stay (d M t : ℕ) (hS : RegStrongFacet d M t)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) (h2 : ∃ l, 2 ≤ x l)
    (h : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1) :
    odoUnif d (2 * M) (t + 1) x = odoUnif d (2 * M) t x := by
  obtain ⟨i, j, hij, z, hz2, hzs, hi, hodo⟩ := facet_normal_form d M x hx k hk
  have h1 := (hodo t).1
  have h2' := (hodo t).2
  have h3 := (hodo (t + 1)).1
  have hlow : odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) + 1 := by
    rw [← h1, ← h2']; exact h
  have hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)) := by
    by_cases ht : (t : ℕ∞) < toppleTime (i + 1 + j) M
    · exact Or.inl ht
    · exact Or.inr ⟨hi h2, le_of_not_gt ht⟩
  have hS' := hS i j hij z hz2 hzs hreg hlow
  rw [h3, h1]; exact hS'.1

/-- The raw form of weak facet compatibility, from the clause at facet points. -/
theorem weak_facet_step_of_reg (d M q : ℕ) (hq : 1 ≤ q) (hW : RegWeak d M q) :
    weak_facet_step d M q := by
  intro z k hz hk h
  exact weak_raw d M q hq hW z hz.1 k hk h

/-- The raw form of strong facet compatibility, from the clause at facet points
and the first-difference bound. -/
theorem strong_facet_step_of_reg (d M q : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (_hS : RegStrongFacet d M q) : strong_facet_step d M q := by
  intro z k hz hk
  have h1 := odo_first_diff d M hd hM q k z (by rw [hk])
  rw [hk] at h1
  linarith

/-- The toppling form of strong facet compatibility at a raw point, from the
clause at facet points. -/
theorem strong_facet_step_topple_of_reg (d M q : ℕ) (hS : RegStrongFacet d M q) :
    strong_facet_step_topple d M q := by
  intro z k hz hk h2 h
  exact ⟨strong_raw_stay d M q hS z hz.1 k hk h2 h,
    strong_raw d M q hS z hz.1 k hk h2 h⟩

/-- The strong topple step predicate, from the clause at every time. -/
theorem strong_topple_control_step_of_reg (d M : ℕ) (hT : ∀ q, RegTopple d M q) :
    strong_topple_control_step d M :=
  fun s hs => hT s hs

/-- The self-similarity step predicate, from the clause at every time. -/
theorem self_similarity_step_of_reg (d M : ℕ) (hC : ∀ q, RegConsist d M q) :
    self_similarity_step d M :=
  fun j hj1 hj2 s hs z hz hzgt => hC s j hj1 hj2 hs z hz hzgt

end DimRed
