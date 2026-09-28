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

/-- The toppling at the previous time, from the facet gap at the current time and
the toppling form of the clause one step back. -/
theorem odo_jump_of_gap {d M t : ℕ} (hd : 1 ≤ d) (hM : 2 ≤ M) (ht : 2 ≤ t)
    (hS : RegStrongFacet d M (t - 2))
    (x : Site d) (hx : inSimplex d M x) (k : Fin d) (hk : x k = 1)
    (h2 : ∃ l, 2 ≤ x l)
    (hgap : odoUnif d (2 * M) (t - 1) x = odoUnif d (2 * M) (t - 1) (x + unit k) + 1) :
    odoUnif d (2 * M) (t - 1) x = odoUnif d (2 * M) (t - 2) x + 1 := by
  have hstep : odoUnif d (2 * M) (t - 1) x ≤ odoUnif d (2 * M) (t - 2) x + 1 := by
    have hsub := (odo_succ_sub_bounds d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 2) x).2
    have ht1 : t - 2 + 1 = t - 1 := by omega
    have hsub' : odoUnif d (2 * M) (t - 1) x - odoUnif d (2 * M) (t - 2) x ≤ 1 := by
      rw [← ht1]
      exact hsub
    omega
  have hmono : odoUnif d (2 * M) (t - 2) x ≤ odoUnif d (2 * M) (t - 1) x :=
    odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (by omega : t - 2 ≤ t - 1) x
  have hmono' : odoUnif d (2 * M) (t - 2) (x + unit k) ≤ odoUnif d (2 * M) (t - 1) (x + unit k) :=
    odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (by omega : t - 2 ≤ t - 1) (x + unit k)
  have hfirst : odoUnif d (2 * M) (t - 2) x - odoUnif d (2 * M) (t - 2) (x + unit k) ≤ 1 := by
    have h := odo_first_diff d M hd (by omega) (t - 2) k x (by rw [hk])
    rw [hk] at h
    exact h
  by_contra hne
  have heq : odoUnif d (2 * M) (t - 1) x = odoUnif d (2 * M) (t - 2) x := by
    by_contra hne2
    exact hne (by omega)
  have hgap2 : odoUnif d (2 * M) (t - 2) x = odoUnif d (2 * M) (t - 2) (x + unit k) + 1 := by
    omega
  have htopple := strong_raw d M (t - 2) hS x hx.1 k hk h2 hgap2
  have ht1 : t - 2 + 1 = t - 1 := by omega
  rw [ht1] at htopple
  omega

/-- The paper's Case 1 derivation: at the topple time `T` of the smaller cube,
the odometer one step later at height `y` equals the smaller cube's odometer at
`y - 1`, because the two neighbours at time `T` are the smaller cube's values. -/
theorem one_dim_consist_derived (M T : ℕ) (hM : 2 ≤ M)
    (hT : toppleTime 1 (M - 1) = (T : ℕ∞))
    (hconsT : RegConsist 1 M T)
    (y : ℤ) (hy3 : 3 ≤ y) (hyM : y ≤ (M : ℤ)) :
    odoUnif 1 (2 * M) (T + 1) (fun _ => y)
      = odoUnif 1 (2 * (M - 1)) (T + 1) (fun _ => y - 1) := by
  -- the clause at time `T` at the point `y` and at `y - 1`
  have hy1 : 2 ≤ y := by omega
  have hyM1 : y ≤ (M : ℤ) := hyM
  have hM1 : 1 ≤ M - 1 := by omega
  have hsub : ((M : ℤ) - ((M - 1 : ℕ) : ℤ)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hpoint : (fun i : Fin 1 => y - ((M : ℤ) - ((M - 1 : ℕ) : ℤ)))
      = (fun _ : Fin 1 => y - 1) := by
    funext i
    rw [hsub]
  have hTle : (T : ℕ∞) ≤ toppleTime 1 (M - 1) := by rw [hT]
  have h1 := hconsT (M - 1) hM1 (by omega) hTle (fun _ : Fin 1 => y)
    (by
      constructor
      · intro i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        exact ⟨by linarith, hyM⟩
      · intro i j _
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        have hj : j = (0 : Fin 1) := Fin.eq_zero j
        rw [hi, hj])
    (fun i => by
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      change (M : ℤ) - ((M - 1 : ℕ) : ℤ) < y
      rw [hsub]
      omega)
  rw [hpoint] at h1
  simp only [odoUnif] at h1
  norm_num at h1
  -- the induction step at `T` and at `T + 1`
  have hstep := Frozen.pt_ind_lemma 1 (2 * M) (by norm_num) (fun _ => 2)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) T (fun _ : Fin 1 => y)
    (by
      intro i
      rw [loCoord_two_mul, hiCoord_two_mul]
      exact ⟨by linarith, hyM⟩)
  have hstep' := Frozen.pt_ind_lemma 1 (2 * (M - 1)) (by norm_num) (fun _ => 2)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) T (fun _ : Fin 1 => y - 1)
    (by
      intro i
      rw [loCoord_two_mul, hiCoord_two_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      norm_num
      exact ⟨by omega, by omega⟩)
  -- the neighbour sums at the two points
  have hnbr : nbrSum (odo 1 (2 * M) (fun _ => 2) T) (fun _ : Fin 1 => y)
      = odo 1 (2 * M) (fun _ => 2) T (fun _ => y + 1)
        + odo 1 (2 * M) (fun _ => 2) T (fun _ => y - 1) := by
    simp only [nbrSum, Fin.sum_univ_one]
    rw [site_one_add_unit, site_one_sub_unit]
  have hnbr' : nbrSum (odo 1 (2 * (M - 1)) (fun _ => 2) T) (fun _ : Fin 1 => y - 1)
      = odo 1 (2 * (M - 1)) (fun _ => 2) T (fun _ => y)
        + odo 1 (2 * (M - 1)) (fun _ => 2) T (fun _ => y - 2) := by
    simp only [nbrSum, Fin.sum_univ_one]
    rw [site_one_add_unit, site_one_sub_unit]
    congr 2
    · funext i
      ring
    · funext i
      ring
  rw [hnbr] at hstep
  rw [hnbr'] at hstep'
  -- the clause at time `T` at the three heights
  have hclause : ∀ (z : ℤ), 2 ≤ z → z ≤ (M : ℤ) →
      odo 1 (2 * M) (fun _ => 2 * (1 : ℤ)) T (fun _ => z)
        = odo 1 (2 * (M - 1)) (fun _ => 2 * (1 : ℤ)) T (fun _ => z - 1) := by
    intro z hz2 hzM
    have h := hconsT (M - 1) hM1 (by omega) (by rw [hT]) (fun _ : Fin 1 => z)
      (by
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          exact ⟨by linarith, hzM⟩
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj])
      (fun i => by
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        change (M : ℤ) - ((M - 1 : ℕ) : ℤ) < z
        rw [hsub]
        omega)
    have hpoint' : (fun i : Fin 1 => z - ((M : ℤ) - ((M - 1 : ℕ) : ℤ)))
        = (fun _ : Fin 1 => z - 1) := by
      funext i
      rw [hsub]
    rw [hpoint'] at h
    simpa only [odoUnif, Nat.cast_one, mul_one] using h
  have h1 : odo 1 (2 * M) (fun _ => 2) T (fun _ => y + 1)
      = odo 1 (2 * (M - 1)) (fun _ => 2) T (fun _ => y) := by
    by_cases hyM' : y + 1 ≤ (M : ℤ)
    · have h := hclause (y + 1) (by omega) hyM'
      simpa using h
    · -- `y = M`: the point `y + 1` is off the cube, and so is `y` in the
      -- smaller cube
      have hyMeq : y = (M : ℤ) := by omega
      rw [hyMeq]
      have hoff : ¬ inCube 1 (2 * M) (fun _ : Fin 1 => (M : ℤ) + 1) := by
        intro hc
        have h := hc ⟨0, by omega⟩
        rw [loCoord_two_mul, hiCoord_two_mul] at h
        simp only at h
        omega
      have hoff' : ¬ inCube 1 (2 * (M - 1)) (fun _ : Fin 1 => (M : ℤ)) := by
        intro hc
        have h := hc ⟨0, by omega⟩
        rw [loCoord_two_mul, hiCoord_two_mul] at h
        rw [Nat.cast_sub (by omega : 1 ≤ M)] at h
        simp only at h
        omega
      rw [odo_eq_zero_outside 1 (2 * M) (fun _ => 2) T _ hoff,
        odo_eq_zero_outside 1 (2 * (M - 1)) (fun _ => 2) T _ hoff']
  have h2 : odo 1 (2 * M) (fun _ => 2) T (fun _ => y - 1)
      = odo 1 (2 * (M - 1)) (fun _ => 2) T (fun _ => y - 2) := by
    have h := hclause (y - 1) (by omega) (by omega)
    have hpt : (fun _ : Fin 1 => y - 1 - 1) = (fun _ : Fin 1 => y - 2) := by
      funext i
      ring
    rw [hpt] at h
    exact h
  rw [h1, h2] at hstep
  exact hstep.trans hstep'.symm

/-- The strong facet compatibility clause at a facet point, in the form the
loaded-spring argument consumes: if the `1`-point is one above the `2`-point at
time `n`, then the `2`-point topples at time `n`. -/
theorem strong_facet_at_point (i j m n : ℕ) (hi : 1 ≤ i) (z : Fin i → ℤ) (hz2 : ∀ a, 2 ≤ z a)
    (hzs : inSimplex (i + 1 + j) m (facetPoint z 1 j))
    (hS : RegStrongFacet (i + 1 + j) m n)
    (hgap : odoUnif (i + 1 + j) (2 * m) n (facetPoint z 1 j)
      = odoUnif (i + 1 + j) (2 * m) n (facetPoint z 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * m) (n + 1) (facetPoint z 2 j)
      = odoUnif (i + 1 + j) (2 * m) n (facetPoint z 2 j) + 1 := by
  have hreg : (n : ℕ∞) < toppleTime (i + 1 + j) m ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) m ≤ (n : ℕ∞)) := by
    by_cases h : (n : ℕ∞) < toppleTime (i + 1 + j) m
    · exact Or.inl h
    · exact Or.inr ⟨hi, not_lt.mp h⟩
  exact (hS i j rfl z hz2 hzs hreg hgap).2

end DimRed
