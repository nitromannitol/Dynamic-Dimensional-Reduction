/-
The weak facet step of the joint induction of `dimred-corrected-arxiv.tex:943-954`: weak facet compatibility
at a triple, from strong facet compatibility at the same triple.
-/
import DimRed.Support.RegInduction
import DimRed.Support.WeakFacetLower
import DimRed.Support.FacetLapUncond
import DimRed.Support.SnocSimplex

namespace DimRed

open LatticeProb

/-- Helper lemma: peel `j` trailing ones from `facetPoint x 1 j` to get `inSimplex i M x`. -/
lemma peel_inSimplex {i j : ℕ} (x : Fin i → ℤ) (M : ℕ) (hM : 1 ≤ M)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) : inSimplex i M x := by
  induction' j with m ih
  · rw [facetPoint_zero] at hxs
    exact ((inSimplex_snoc_one hM x).mp hxs)
  · rw [facetPoint_succ] at hxs
    have htemp : inSimplex ((i + 1 + m) + 1) M (Fin.snoc (facetPoint x 1 m) 1) := by
      convert hxs using 1
      omega
    have hpeeled : inSimplex (i + 1 + m) M (facetPoint x 1 m) :=
      ((inSimplex_snoc_one hM (facetPoint x 1 m)).mp htemp)
    exact ih hpeeled

/-- If `inSimplex` holds for `facetPoint x 1 j`, then it also holds for
`facetPoint x 2 k` for any `k ≤ j`.  This is because `x a ≥ 2` for all `a`. -/
lemma inSimplex_facetPoint_two_of_inSimplex_facetPoint_one {M i j k : ℕ} (x : Fin i → ℤ)
    (hM : 2 ≤ M) (hx2 : ∀ a, 2 ≤ x a) (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) (hk : k ≤ j) :
    inSimplex (i + 1 + k) M (facetPoint x 2 k) := by
  have hM1 : 1 ≤ M := by omega
  have hx_in : inSimplex i M x := peel_inSimplex x M hM1 hxs
  -- Now build inSimplex for facetPoint x 2 k by induction on k
  induction' k with m ih
  · -- k = 0
    rw [facetPoint_zero]
    rw [inSimplex_snoc]
    exact ⟨hx_in, by omega, by omega, hx2⟩
  · -- k = m+1
    have hk' : m ≤ j := by omega
    have hxs_inner : inSimplex (i + 1 + m) M (facetPoint x 2 m) :=
      ih hk'
    rw [facetPoint_succ]
    -- Goal: inSimplex (i + 1 + (m + 1)) M (Fin.snoc (facetPoint x 2 m) 1)
    -- hxs_inner: inSimplex (i + 1 + m) M (facetPoint x 2 m)
    -- inSimplex_snoc_one gives equivalence with (i+1+m)+1 instead of i+1+(m+1)
    convert ((inSimplex_snoc_one hM1 (facetPoint x 2 m)).mpr hxs_inner) using 1
    omega

/-- Dimensional reduction applied `j` times to peel trailing ones from a facet point,
reducing dimension `i+1+j` to `i+1`.  The proof is by induction on `j`.
The first peel uses `hred` (which provides `DimRedAt` at the current dimension);
each subsequent peel uses `hearlier` (which provides `DimRedAt` at strictly smaller
dimensions). -/
lemma odoUnif_facetPoint_reduce (M i j : ℕ) (hM : 2 ≤ M)
    (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hred : ∀ s : ℕ, DimRedAt (i + 1 + j) M s)
    (hearlier : ∀ d' M' t' : ℕ, regEarlier (i + 1 + j) M 0 d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)) :
    (∀ s : ℕ, odoUnif (i + 1 + j) (2 * M) s (facetPoint x 1 j) =
      odoUnif (i + 1) (2 * M) s (facetPoint x 1 0)) ∧
    (∀ s : ℕ, odoUnif (i + 1 + j) (2 * M) s (facetPoint x 2 j) =
      odoUnif (i + 1) (2 * M) s (facetPoint x 2 0)) := by
  have hM1 : 1 ≤ M := by omega
  induction' j with k ih
  · -- j = 0: both sides are Fin.snoc x 1 / Fin.snoc x 2, trivially equal
    constructor
    · intro s; rfl
    · intro s; rfl
  · -- j = k+1
    have hxs1 : inSimplex (i + 1 + k) M (facetPoint x 1 k) := by
      have hxs' := hxs
      rw [facetPoint_succ] at hxs'
      simpa [add_assoc] using ((inSimplex_snoc_one hM1 (facetPoint x 1 k)).mp hxs')
    have hxs2 : inSimplex (i + 1 + k) M (facetPoint x 2 k) :=
      inSimplex_facetPoint_two_of_inSimplex_facetPoint_one x hM hx2 hxs (by omega)
    -- Get DimRedAt at dimension i+1+k from hearlier (since i+1+k < i+1+(k+1))
    have hred_k (s : ℕ) : DimRedAt (i + 1 + k) M s := by
      have h_lt : i + 1 + k < i + 1 + (k + 1) := by omega
      have h_reg_earlier : regEarlier (i + 1 + (k + 1)) M 0 (i + 1 + k) M s :=
        Or.inl h_lt
      exact ((hearlier (i + 1 + k) M s h_reg_earlier (by omega) hM).2)
    -- Adapt hearlier from dimension i+1+(k+1) to i+1+k
    have hearlier_small : ∀ d' M' t' : ℕ, regEarlier (i + 1 + k) M 0 d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t' := by
      intro d' M' t' hreg hd' hM'
      have hreg' : regEarlier (i + 1 + (k + 1)) M 0 d' M' t' := by
        rcases hreg with (hlt | h | h)
        · -- hlt : d' < i + 1 + k
          exact Or.inl (Nat.lt_of_lt_of_le hlt (by omega))
        · -- h : d' = i + 1 + k ∧ M' < M
          rcases h with ⟨heq, hMlt⟩
          exact Or.inl (by omega)
        · -- h : d' = i + 1 + k ∧ M' = M ∧ t' < 0
          rcases h with ⟨heq, hMeq, htlt⟩
          exact Or.inl (by omega)
      exact hearlier d' M' t' hreg' hd' hM'
    -- Apply the induction hypothesis
    have ih_res := ih hred_k hearlier_small hxs1
    have ih1 := ih_res.1
    have ih2 := ih_res.2
    constructor
    · intro s
      calc
        odoUnif (i + 1 + (k + 1)) (2 * M) s (facetPoint x 1 (k + 1)) =
            odoUnif (i + 1 + (k + 1)) (2 * M) s (Fin.snoc (facetPoint x 1 k) 1) := by
          rw [facetPoint_succ]
        _ = odoUnif ((i + 1 + k) + 1) (2 * M) s (Fin.snoc (facetPoint x 1 k) 1) := by
          congr 1
        _ = odoUnif (i + 1 + k) (2 * M) s (facetPoint x 1 k) := by
          rw [hred s (i + 1 + k) (by omega) (by omega) (facetPoint x 1 k) hxs1]
        _ = odoUnif (i + 1) (2 * M) s (facetPoint x 1 0) := ih1 s
    · intro s
      calc
        odoUnif (i + 1 + (k + 1)) (2 * M) s (facetPoint x 2 (k + 1)) =
            odoUnif (i + 1 + (k + 1)) (2 * M) s (Fin.snoc (facetPoint x 2 k) 1) := by
          rw [facetPoint_succ]
        _ = odoUnif ((i + 1 + k) + 1) (2 * M) s (Fin.snoc (facetPoint x 2 k) 1) := by
          congr 1
        _ = odoUnif (i + 1 + k) (2 * M) s (facetPoint x 2 k) := by
          rw [hred s (i + 1 + k) (by omega) (by omega) (facetPoint x 2 k) hxs2]
        _ = odoUnif (i + 1) (2 * M) s (facetPoint x 2 0) := ih2 s

/-- The weak facet step of the joint induction: `RegWeak` at one triple from strong facet
compatibility at the SAME triple.

With an empty head (`i = 0`) the point is the all-ones point and the clause is unconditional,
`FacetLapUncond.odo_succ_facetPoint_zero_of`.  With a nonempty head, whatever the tail, the first
conjunct of `RegStrongFacet` is literally this conclusion, and its regime hypothesis
`t < τ_M ∨ (1 ≤ i ∧ τ_M ≤ t)` holds for free: the trichotomy on `t` against `τ_M` supplies one
disjunct or the other.  So no descent through the dimensions is needed, and the earlier
instances are not used.

Consequence for the induction: weak facet at a triple consumes strong facet at the same triple,
so strong facet at a triple must be proved WITHOUT weak facet at that triple. -/
theorem weak_step_of_earlier (d M t : ℕ) (_hd : 1 ≤ d) (_hM : 2 ≤ M)
    (_hearlier : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hfacet : RegStrongFacet d M t) :
    RegWeak d M t := by
  intro i j h_eq hi x hx2 hxs heq
  -- h_eq : i + 1 + j = d
  -- hi : 1 ≤ t
  -- hx2 : ∀ a, 2 ≤ x a
  -- hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j)
  -- heq : odoUnif d (2 * M) t (facetPoint x 1 j) = odoUnif d (2 * M) t (facetPoint x 2 j) + 1
  rcases Nat.eq_zero_or_pos i with (rfl | hi_pos)
  · -- Case 1: i = 0, the point is the all-ones point
    have := odo_succ_facetPoint_zero_of x t heq
    simpa [h_eq] using this
  · -- i ≥ 1
    by_cases hj : j = 0
    · -- Case 3: j = 0, use hfacet directly
      subst hj
      -- h_eq : i + 1 + 0 = d, so d = i + 1
      have h_eq_symm : d = i + 1 + 0 := by omega
      -- Use trichotomy on t vs toppleTime d M
      by_cases ht : (t : ℕ∞) < toppleTime d M
      · have hregime : (t : ℕ∞) < toppleTime (i + 1 + 0) M ∨ (1 ≤ i ∧ toppleTime (i + 1 + 0) M ≤ (t : ℕ∞)) := by
          rw [← h_eq_symm]
          exact Or.inl ht
        exact (hfacet i 0 (by omega) x hx2 hxs hregime heq).1
      · have htp : toppleTime d M ≤ (t : ℕ∞) := le_of_not_gt ht
        have hregime : (t : ℕ∞) < toppleTime (i + 1 + 0) M ∨ (1 ≤ i ∧ toppleTime (i + 1 + 0) M ≤ (t : ℕ∞)) := by
          rw [← h_eq_symm]
          exact Or.inr ⟨by omega, htp⟩
        exact (hfacet i 0 (by omega) x hx2 hxs hregime heq).1
    · -- Case 2: i ≥ 1, j ≥ 1
      have hj_pos : 1 ≤ j := by omega
      -- Use hfacet directly: the first conjunct of RegStrongFacet is exactly RegWeak
      by_cases ht : (t : ℕ∞) < toppleTime (i + 1 + j) M
      · have hregime : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨ (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)) := Or.inl ht
        exact (hfacet i j (by omega) x hx2 hxs hregime heq).1
      · have htp : toppleTime (i + 1 + j) M ≤ (t : ℕ∞) := le_of_not_gt ht
        have hregime : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨ (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)) := Or.inr ⟨hi_pos, htp⟩
        exact (hfacet i j (by omega) x hx2 hxs hregime heq).1

end DimRed
