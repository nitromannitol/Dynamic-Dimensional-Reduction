import DimRed.Support.StrongDerivRaw
import DimRed.Support.StrongDerivEarly
import DimRed.Support.SnocSimplex

/-!
# The strong derivative clause at one triple

The strong derivative clause of Proposition 4.1 at one triple, from the two
branches of the paper's Section 5 argument.

With a nonempty head (`1 ≤ i`) the clause is `strong_deriv_pos_head`, which
consumes the pure second difference `odo_pure_diff` of the positive orthant at
every earlier time.  With an empty head the point is the all-ones point `1_d`
and the clause is `strong_deriv_zero_head`, which is the early-time Case 1 of
`dimred.tex:1322-1332`; the regime hypothesis `hreg` then forces `t < τ_M`,
because the second disjunct requires `1 ≤ i`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- A facet point with an empty head is `c` at the first coordinate and `1`
elsewhere. -/
theorem facetPoint_zero_head (c : ℤ) (j : ℕ) :
    facetPoint (fun _ : Fin 0 => (0 : ℤ)) c j
      = fun k : Fin (0 + 1 + j) => if k = (⟨0, by omega⟩ : Fin (0 + 1 + j)) then c else 1 := by
  have hsnoc : (Fin.snoc (fun _ : Fin 0 => (0 : ℤ)) c : Fin (0 + 1) → ℤ)
      = fun _ => c := by
    funext a
    have ha : a = Fin.last 0 := Fin.eq_zero a
    subst ha
    rw [Fin.snoc_last]
  funext k
  rw [facetPoint, hsnoc]
  refine Fin.addCases ?_ (fun b => ?_) k
  · intro a
    have ha : a = (Fin.last 0 : Fin 1) := Fin.eq_zero a
    subst ha
    rw [Fin.append_left]
    have hcast : (Fin.castAdd j (Fin.last 0) : Fin (0 + 1 + j))
        = (⟨0, by omega⟩ : Fin (0 + 1 + j)) := by
      ext
      rfl
    rw [hcast, if_pos rfl]
  · rw [Fin.append_right]
    have hne : (Fin.natAdd (0 + 1) b : Fin (0 + 1 + j))
        ≠ (⟨0, by omega⟩ : Fin (0 + 1 + j)) := by
      intro h
      have h1 : (Fin.natAdd (0 + 1) b : Fin (0 + 1 + j)).val = 0 + 1 + b.val := rfl
      have h2 : ((⟨0, by omega⟩ : Fin (0 + 1 + j))).val = 0 := rfl
      rw [h] at h1
      omega
    rw [if_neg hne]

/-- The strong derivative clause at one triple, from the earlier instances of
the joint induction.  The earlier instances enter only through weak facet
compatibility at times below `t`, which is what `odo_pure_diff` and
`odo_two_diff_early` consume. -/
theorem deriv_step_of_earlier (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    RegStrongDeriv d M t := by
  intro i j hij x hx2 hxs hreg
  have hd' : 1 ≤ i + 1 + j := by omega
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- empty head: the point is the all-ones point, and `hreg` forces `t < τ_M`
    have ht : (t : ℕ∞) < toppleTime (0 + 1 + j) M := by
      rcases hreg with h | ⟨h1, _⟩
      · exact h
      · exact absurd h1 (by omega)
    have hW : ∀ s, 1 ≤ s → s < t → RegWeak (0 + 1 + j) M s := by
      intro s hs hst
      have he : regEarlier d M t (0 + 1 + j) M s :=
        Or.inr (Or.inr ⟨hij, rfl, hst⟩)
      have hd'' : 1 ≤ 0 + 1 + j := by omega
      exact (hprior (0 + 1 + j) M s he hd'' hM).1.2.1
    have h := strong_deriv_zero_head (0 + 1 + j) M t (by omega) hM hW ht
    have hx0 : x = fun _ : Fin 0 => (0 : ℤ) := funext fun a => absurd a.2 (by omega)
    have h1 : facetPoint x 1 j = fun _ : Fin (0 + 1 + j) => (1 : ℤ) := by
      rw [hx0, facetPoint_zero_head]
      funext k
      by_cases hk : k = (⟨0, by omega⟩ : Fin (0 + 1 + j))
      · rw [if_pos hk]
      · rw [if_neg hk]
    have h3 : facetPoint x 3 j
        = fun k : Fin (0 + 1 + j) =>
            if k = (⟨0, by omega⟩ : Fin (0 + 1 + j)) then 3 else 1 := by
      rw [hx0, facetPoint_zero_head]
    rw [h1, h3]
    exact h
  · -- nonempty head: the pure second difference at every earlier time
    have hpure : ∀ s, s ≤ t → ∀ (k : Fin (i + 1 + j)) (y : Site (i + 1 + j)),
        inPos (i + 1 + j) M y → (∃ l, y k < y l) →
        odoUnif (i + 1 + j) (2 * M) s y
          - odoUnif (i + 1 + j) (2 * M) s (y + unit k + unit k) ≤ 2 * y k := by
      intro s hs k y hy hmax
      have hW : ∀ r, 1 ≤ r → r < s → RegWeak (i + 1 + j) M r := by
        intro r hr hrs
        have he : regEarlier d M t (i + 1 + j) M r :=
          Or.inr (Or.inr ⟨hij, rfl, by omega⟩)
        have hd'' : 1 ≤ i + 1 + j := by omega
        exact (hprior (i + 1 + j) M r he hd'' hM).1.2.1
      have hS : ∀ r, r < s → RegStrongFacet (i + 1 + j) M r := by
        intro r hrs
        have he : regEarlier d M t (i + 1 + j) M r :=
          Or.inr (Or.inr ⟨hij, rfl, by omega⟩)
        have hd'' : 1 ≤ i + 1 + j := by omega
        exact (hprior (i + 1 + j) M r he hd'' hM).1.2.2.2.1
      exact odo_pure_diff (i + 1 + j) M s (by omega) (by omega) hW hS s le_rfl k y hy hmax
    exact strong_deriv_pos_head M i j t hM hi hpure x hx2 hxs

end DimRed
