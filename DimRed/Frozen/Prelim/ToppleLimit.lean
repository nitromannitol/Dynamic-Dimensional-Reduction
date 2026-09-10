/-
Lemma 2.5 of `dimred.tex`, frozen.  `dimred.tex:669-674` (label `topple_limit`):

  "For all $t \geq t_0$ and $j \geq 0$,
   $\max_{z \in \mathcal{S}} ( v_{t+j}(z) - v_t(z) ) \leq
    \max_{z \in \mathcal{S}} ( v_{t_0+j}(z) - v_{t_0}(z) )$."

`\mathcal{S}` is `S_M^{(d)}`, the sorted fundamental domain of `C_{2M}^{(d)}`,
and `v_t` on it is the odometer of the hypercube (`symmetry_lemma`; see
CORRESPONDENCE.md).  The standing hypotheses at this point of Section 2 are
carried: the bound `0 ≤ s_0 ≤ 2(2d) - 1` of `dimred.tex:286-288` as `hs0` and
`hs1`, and the symmetry of the initial sandpile of `dimred.tex:400-402` as
`hsym`, without which the maximum over a fundamental domain says nothing about
the rest of the cube.
-/
import DimRed.Support.Fundamental
import DimRed.Support.Stabilize
import DimRed.Frozen.Prelim.PtInd

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.topple_limit (d M : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d (2 * M) y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d (2 * M) y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (hsym : IsSymmetricPile d (2 * M) s₀) (t₀ t j : ℕ) (ht : t₀ ≤ t) :
    simplexMax d M (fun z => odo d (2 * M) s₀ (t + j) z - odo d (2 * M) s₀ t z) ≤
      simplexMax d M (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
-- FROZEN-STATEMENT-END
:= by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set K : ℤ := simplexMax d M
    (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact simplexMax_nonneg d M _ fun z => by
      have := odo_mono d (2 * M) s₀ (Nat.le_add_right t₀ j) z
      linarith
  have hbase : ∀ y, odo d (2 * M) s₀ (t₀ + j) y - odo d (2 * M) s₀ t₀ y ≤ K := by
    intro y
    by_cases hy : inCube d (2 * M) y
    · have hz := inSimplex_toSimplexPoint d M y hy
      have e1 := odo_toSimplexPoint d M s₀ hsym (t₀ + j) y
      have e2 := odo_toSimplexPoint d M s₀ hsym t₀ y
      have hle := le_simplexMax d M
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
        (toSimplexPoint d M y) hz
      simp only [e1, e2] at hle
      exact hle
    · rw [odo_eq_zero_outside d (2 * M) s₀ (t₀ + j) y hy,
        odo_eq_zero_outside d (2 * M) s₀ t₀ y hy]
      simpa using hKnn
  have hstep : ∀ n y, odo d (2 * M) s₀ (t₀ + n + j) y - odo d (2 * M) s₀ (t₀ + n) y ≤ K := by
    intro n
    induction n with
    | zero => intro y; simpa using hbase y
    | succ m ih =>
      intro y
      by_cases hy : inCube d (2 * M) y
      · rw [show t₀ + (m + 1) + j = (t₀ + m + j) + 1 from by omega,
          show t₀ + (m + 1) = (t₀ + m) + 1 from by omega,
          Frozen.pt_ind_lemma d (2 * M) hd s₀ hs0 hs1 (t₀ + m + j) y hy,
          Frozen.pt_ind_lemma d (2 * M) hd s₀ hs0 hs1 (t₀ + m) y hy]
        have hle : nbrSum (odo d (2 * M) s₀ (t₀ + m + j)) y
            ≤ nbrSum (fun z => odo d (2 * M) s₀ (t₀ + m) z + K) y :=
          nbrSum_mono (fun z => by have := ih z; linarith) y
        rw [nbrSum_add_const] at hle
        have h1 : (s₀ y + nbrSum (odo d (2 * M) s₀ (t₀ + m + j)) y) / (2 * (d : ℤ))
            ≤ (s₀ y + (nbrSum (odo d (2 * M) s₀ (t₀ + m)) y + 2 * (d : ℤ) * K))
                / (2 * (d : ℤ)) :=
          Int.ediv_le_ediv hdpos (by linarith)
        have h2 : (s₀ y + (nbrSum (odo d (2 * M) s₀ (t₀ + m)) y + 2 * (d : ℤ) * K))
            / (2 * (d : ℤ))
            = (s₀ y + nbrSum (odo d (2 * M) s₀ (t₀ + m)) y) / (2 * (d : ℤ)) + K := by
          rw [show s₀ y + (nbrSum (odo d (2 * M) s₀ (t₀ + m)) y + 2 * (d : ℤ) * K)
              = (s₀ y + nbrSum (odo d (2 * M) s₀ (t₀ + m)) y) + 2 * (d : ℤ) * K from by ring]
          exact Int.add_mul_ediv_left _ K (by linarith)
        rw [h2] at h1
        linarith
      · rw [odo_eq_zero_outside d (2 * M) s₀ (t₀ + (m + 1) + j) y hy,
          odo_eq_zero_outside d (2 * M) s₀ (t₀ + (m + 1)) y hy]
        simpa using hKnn
  refine simplexMax_le d M _ K hKnn ?_
  intro z _
  have h := hstep (t - t₀) z
  rw [show t₀ + (t - t₀) = t from by omega] at h
  exact h
