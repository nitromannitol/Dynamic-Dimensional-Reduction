/-
The second half of the strong-derivative route of
`scratch/case2-2026-09-24/lean-plan.md`: the raw forms of weak and strong facet
compatibility at a point of the positive orthant, obtained from the facet normal
form, and the estimates that consume them.
-/
import DimRed.Support.StrongDerivPure
import DimRed.Support.FacetNormal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- Weak facet compatibility at a raw point of the positive orthant, from the
clause at the facet normal form. -/
theorem weak_raw (d M t : ℕ) (ht : 1 ≤ t) (hW : RegWeak d M t)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1)
    (h : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1) :
    odoUnif d (2 * M) (t + 1) x = odoUnif d (2 * M) t x := by
  obtain ⟨i, j, hij, z, hz2, hzs, hi, hodo⟩ := facet_normal_form d M x hx k hk
  have h1 := (hodo t).1
  have h2 := (hodo t).2
  have h3 := (hodo (t + 1)).1
  have hlow : odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) + 1 := by
    rw [← h1, ← h2]; exact h
  have hW' := hW i j hij ht z hz2 hzs hlow
  rw [h3, h1]; exact hW'

/-- Strong facet compatibility at a raw point of the positive orthant, from the
clause at the facet normal form. -/
theorem strong_raw (d M t : ℕ) (hS : RegStrongFacet d M t)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) (h2 : ∃ l, 2 ≤ x l)
    (h : odoUnif d (2 * M) t x = odoUnif d (2 * M) t (x + unit k) + 1) :
    odoUnif d (2 * M) (t + 1) (x + unit k) = odoUnif d (2 * M) t (x + unit k) + 1 := by
  obtain ⟨i, j, hij, z, hz2, hzs, hi, hodo⟩ := facet_normal_form d M x hx k hk
  have h1 := (hodo t).1
  have h2' := (hodo t).2
  have h4 := (hodo (t + 1)).2
  have hlow : odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) =
      odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) + 1 := by
    rw [← h1, ← h2']; exact h
  have hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)) := by
    by_cases ht : (t : ℕ∞) < toppleTime (i + 1 + j) M
    · exact Or.inl ht
    · exact Or.inr ⟨hi h2, le_of_not_gt ht⟩
  have hS' := (hS i j hij z hz2 hzs hreg hlow).2
  rw [h4, h2']; exact hS'

/-- The facet lag bound `eq:facet_lag`, `dimred.tex:1374-1379`. -/
theorem odo_facet_lag (d M T : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hS : ∀ s, s < T → RegStrongFacet d M s) (s : ℕ) (hs : s + 1 ≤ T)
    (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) (h2 : ∃ l, 2 ≤ x l) :
    odoUnif d (2 * M) s x ≤ odoUnif d (2 * M) (s + 1) (x + unit k) := by
  have hxk1 : (1 : ℤ) ≤ x k := by rw [hk]
  have hfirst := odo_first_diff d M hd hM s k x hxk1
  by_cases heq : odoUnif d (2 * M) s x = odoUnif d (2 * M) s (x + unit k) + 1
  · have hstrong := strong_raw d M s (hS s (by omega)) x hx k hk h2 heq
    omega
  · have hmono : odoUnif d (2 * M) s (x + unit k) ≤ odoUnif d (2 * M) (s + 1) (x + unit k) :=
      odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (Nat.le_succ s) (x + unit k)
    rw [hk] at hfirst
    omega

end DimRed
