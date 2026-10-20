import DimRed.Support.RegSteps
import DimRed.Support.DimRedCritical
import DimRed.Support.OneStep
import DimRed.Support.GapTopple
open LatticeProb DimRed
namespace DimRed

/-- The critical case of dimensional reduction, the subsection titled `Dimensional reduction` in `dimred-corrected-arxiv.tex`, from the
earlier instances of the joint induction.  This is `hcritical` of
`dimred_step_of_earlier`, discharged from `hprior` plus the committed
`odo_dimred_critical`.

The `e = 0` case of `hcritical` is unreachable: `DimRedAt` carries `1 ≤ e`, and
`dimred_step_of_earlier` invokes `hcritical` only at `1 ≤ q` with `1 ≤ e`, so the
statement below takes `1 ≤ e` as a hypothesis.

The remaining input is `hjump`: the head point `Fin.snoc z 1` topples at `t - 1`,
which is the second conjunct of strong facet compatibility at `t - 2` applied to
the point `Fin.snoc z 1` (whose last coordinate is `1`) and its neighbour
`Fin.snoc z 2`.  The gap hypothesis `hgap` is the first conjunct at the same
point. -/
theorem hcritical_from_prior (d M t : ℕ) (_hd : 1 ≤ d) (hM : 2 ≤ M) (ht2 : 2 ≤ t)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    ∀ (e : ℕ) (_he : 1 ≤ e) (_hde : e + 1 = d) (z : Site e), inSimplex e M z →
      (∀ k : Fin e, 1 < z k) →
      odoUnif (e + 1) (2 * M) (t - 1) (Fin.snoc z 1) =
        odoUnif (e + 1) (2 * M) (t - 1)
          (Fin.snoc z 1 + unit (Fin.last e)) + 1 →
      (∀ i : ℕ, 1 ≤ i → i ≤ e → ∀ w : Site i,
          odoUnif (i + 1) (2 * M) (t - 1) (Fin.snoc w 1) =
            odoUnif i (2 * M) (t - 1) w) →
      (weak_facet_step (e + 1) M (t - 1) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ e → weak_facet_step i M (t - 1)) →
      (strong_facet_step (e + 1) M (t - 1) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ e → strong_facet_step i M (t - 1)) →
      (∀ i : ℕ, 1 ≤ i → i ≤ e + 1 →
        (toppleTime i (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞) →
          simplexMax i M (fun w => odoUnif i (2 * M) t w
            - odoUnif i (2 * M) (t - 2) w) ≤ 1)) →
      (∀ (j : ℕ), 1 ≤ j → j ≤ M → ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (e + 1) j →
        ∀ w : Site (e + 1), inSimplex (e + 1) M w →
          (∀ i : Fin (e + 1), (M : ℤ) - (j : ℤ) < w i) →
          odoUnif (e + 1) (2 * M) (t - 1) w =
            odoUnif (e + 1) (2 * j) (t - 1) (fun i => w i - ((M : ℤ) - (j : ℤ)))) →
      odoUnif (e + 1) (2 * M) t (Fin.snoc z 1) =
        odoUnif e (2 * M) t z := by
  intro e he1 hde z hz hz1 hgap hred hweak hstrong htopple hconsist
  have hpt : Fin.snoc z 1 + unit (Fin.last e) = Fin.snoc z 2 := by
    rw [← fin_snoc_add_last z 1]
    norm_num
  apply odo_dimred_critical e M t he1 hM ht2 z hz hz1
  · -- `hprev`: reduction at the two previous times, both scales
    intro s m hs hm2 hmM y hy
    by_cases hmM' : m = M
    · rw [hmM'] at hy ⊢
      exact (hprior (e + 1) M s (Or.inr (Or.inr ⟨hde, rfl, by omega⟩))
        (by omega) hM).2 e (by omega) rfl y hy
    · exact (hprior (e + 1) m s (Or.inr (Or.inl ⟨hde, by omega⟩))
        (by omega) hm2).2 e (by omega) rfl y hy
  · -- `hprev_one`: the smallest scale
    intro s hs y hy
    have h1 : inSimplex e 1 y := hy
    have h2 : Fin.snoc y 1 = (fun _ : Fin (e + 1) => (1 : ℤ)) := by
      funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [Fin.snoc]
      · simp only [Fin.snoc_castSucc]
        have hle := (h1.1 i').2
        have hge := (h1.1 i').1
        omega
    have h3 : y = (fun _ : Fin e => (1 : ℤ)) := by
      funext i
      have hle := (h1.1 i).2
      have hge := (h1.1 i).1
      omega
    rw [h2, h3, odoUnif_one_scale (e + 1) s (by omega),
      odoUnif_one_scale e s (by omega)]
  · -- the gap at `t - 1`
    rw [hpt] at hgap
    exact hgap
  · -- the jump at `t - 1`: the head point topples at `t - 1`, which is
    -- `odo_topple_of_gap` applied to the gap `hgap` at `t - 1`
    have hX : inSimplex (e + 1) M (Fin.snoc z 1) :=
      inSimplex_snoc_one_local z hz (by omega)
    have hS : RegStrongFacet (e + 1) M (t - 2) :=
      (hprior (e + 1) M (t - 2) (Or.inr (Or.inr ⟨hde, rfl, by omega⟩))
        (by omega) hM).1.2.2.2.1
    have hlast : (Fin.snoc z 1 : Site (e + 1)) (Fin.last e) = 1 := by
      simp [Fin.snoc]
    have h2 : ∃ l, 2 ≤ (Fin.snoc z 1 : Site (e + 1)) l :=
      ⟨Fin.castSucc ⟨0, by omega⟩, by
        simp only [Fin.snoc_castSucc]
        have := hz1 ⟨0, by omega⟩
        omega⟩
    exact odo_topple_of_gap (e + 1) M (t - 1) (by omega) hM (by omega) hS
      (Fin.snoc z 1) hX (Fin.last e) hlast h2 hgap
  · -- strong topple control in dimension `e+1`
    intro hle
    exact htopple (e + 1) (by omega) (by omega) (by omega)
  · -- strong topple control in dimension `e`
    intro hle
    have hmono : toppleTime e (M - 1) ≤ toppleTime (e + 1) (M - 1) := by
      by_cases hM2 : M = 2
      · subst hM2
        rw [toppleTime_one_eq_one e (by omega), toppleTime_one_eq_one (e + 1) (by omega)]
      · exact toppleTime_mono_dim e (M - 1) he1 (by omega)
          (fun t' y hy => (hprior (e + 1) (M - 1) t'
            (Or.inr (Or.inl ⟨hde, Nat.sub_lt (by omega) (by omega)⟩))
            (by omega) (by omega)).2 e he1 rfl y hy)
          (fun e'' he'' hlt t' y hy => by
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt' | heq
            · exact (hprior (e'' + 1) (M - 1) t'
                (Or.inl (by omega)) (by omega) (by omega)).2 e'' he'' rfl y hy
            · cases heq
              exact (hprior (e + 1) (M - 1) t'
                (Or.inr (Or.inl ⟨hde, Nat.sub_lt (by omega) (by omega)⟩))
                (by omega) (by omega)).2 e he1 rfl y hy)
    exact htopple e he1 (Nat.le_succ e) (le_trans hmono hle)
  · -- self-similarity at scale `M` below the topple time
    intro hle
    have hmono_le : toppleTime (e + 1) (M - 1) ≤ toppleTime e (M - 1) := by
      by_cases hM2 : M = 2
      · subst hM2
        rw [toppleTime_one_eq_one e (by omega), toppleTime_one_eq_one (e + 1) (by omega)]
      · exact toppleTime_mono_dim_le e (M - 1) he1 (by omega)
          (fun t' y hy => (hprior (e + 1) (M - 1) t'
            (Or.inr (Or.inl ⟨hde, Nat.sub_lt (by omega) (by omega)⟩))
            (by omega) (by omega)).2 e he1 rfl y hy)
          (fun e'' he'' hlt t' y hy => by
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt' | heq
            · exact (hprior (e'' + 1) (M - 1) t'
                (Or.inl (by omega)) (by omega) (by omega)).2 e'' he'' rfl y hy
            · cases heq
              exact (hprior (e + 1) (M - 1) t'
                (Or.inr (Or.inl ⟨hde, Nat.sub_lt (by omega) (by omega)⟩))
                (by omega) (by omega)).2 e he1 rfl y hy)
    have hle' : ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime e (M - 1) := le_trans hle hmono_le
    have hM1 : ((M : ℤ) - ((M - 1 : ℕ) : ℤ)) = 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      norm_num
    have hsnoc : (fun i : Fin (e + 1) =>
          (Fin.snoc z (2 : ℤ) : Fin (e + 1) → ℤ) i
            - ((M : ℤ) - ((M - 1 : ℕ) : ℤ)))
        = (Fin.snoc (fun k => z k - 1) (1 : ℤ) : Fin (e + 1) → ℤ) := by
      funext i
      rw [hM1]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [Fin.snoc]
      · simp [Fin.snoc]
    have hshift : (fun k => z k - ((M : ℤ) - ((M - 1 : ℕ) : ℤ))) = fun k => z k - 1 := by
      funext k
      rw [hM1]
    refine ⟨?_, ?_⟩
    · have h1 := hconsist (M - 1) (by omega) (by omega) hle (Fin.snoc z 2)
        (inSimplex_snoc_two_local z hz (fun i => by have := hz1 i; omega) hM)
        (by
          intro i
          rw [hM1]
          refine Fin.lastCases ?_ (fun k => ?_) i
          · simp [Fin.snoc]
          · simp only [Fin.snoc_castSucc]
            exact hz1 k)
      rw [hsnoc] at h1
      exact h1
    · have h2 := (hprior e M (t - 1)
        (Or.inl (by omega))
        he1 hM).1.1 (M - 1) (by omega) (by omega) hle' z hz
        (by intro i; rw [hM1]; exact hz1 i)
      rw [hshift] at h2
      exact h2
end DimRed
