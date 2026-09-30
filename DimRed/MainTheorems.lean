import DimRed.Frozen.Prelim.Symmetry
import DimRed.Frozen.BaseCase.NoReduction
import DimRed.Frozen.BaseCase.RadialLaplacian
import DimRed.Frozen.Prelim.PtInd
import DimRed.Frozen.Prelim.ParabolicComparison
import DimRed.Frozen.Prelim.ToppleLimit
import DimRed.Frozen.Prelim.DifferenceComparison
import DimRed.Frozen.BaseCase.ExplicitOdometer
import DimRed.Frozen.Prelim.AxisMonotonicity
import DimRed.Frozen.Prelim.DerivativeBound
import DimRed.Frozen.Main.DimensionalReduction
import DimRed.Frozen.Main.TerminalReduction
import DimRed.Frozen.Main.SelfSimilarity
import DimRed.Frozen.Main.SandpileReduction
import DimRed.Frozen.Main.SandpileSelfSimilarity
import DimRed.Frozen.Regularity.Consistency
import DimRed.Frozen.Regularity.WeakFacet
import DimRed.Frozen.Regularity.StrongDerivative
import DimRed.Frozen.Regularity.StrongFacet
import DimRed.Frozen.Regularity.StrongTopple

/-!
# Main results

The formalization of *Dynamic dimensional reduction in the Abelian sandpile* (Ahmed
Bou-Rabee) is complete: all twenty registered statements of the paper are proved.  The
main results are Theorem 1.1 and Corollary 1.1, proved together with the five clauses of
Proposition 4.1 by one joint induction over dimension, side length and time (Sections 4
and 5):

* `DimRed.dimensional_reduction`: Theorem 1.1(i), dimensional reduction on the
  centre slice, `v_t^{(d,N)}(x_{d-1}, 1) = v_t^{(d-1,N)}(x_{d-1})` for every `t ≥ 1`.
* `DimRed.terminal_dimensional_reduction`: Theorem 1.1(i), second display,
  `v_∞^{(d,N)}(x_{d-1}, 2) = v_∞^{(d-1,N)}(x_{d-1})` for `x_{d-1} ≥ 2`.
* `DimRed.self_similarity`: Theorem 1.1(ii), self-similarity for `t ≤ τ_j`, with
  the topple time `τ_j` the first time some inner boundary site reaches height `j`.
* `DimRed.sandpile_dimensional_reduction`: Corollary 1.1(i), dimensional
  reduction of the terminal sandpile.
* `DimRed.sandpile_self_similarity`: Corollary 1.1(ii), self-similarity of the
  sandpile.

and the five clauses of Proposition 4.1: `DimRed.base_dimension_consistency`,
`DimRed.base_dimension_weak_compatibility`, `DimRed.base_dimension_strong_derivative`,
`DimRed.base_dimension_strong_compatibility`, `DimRed.base_dimension_strong_topple`.

Every theorem in this file restates its certified counterpart in `DimRed/Frozen/`
unchanged and is proved by `exact` of it, so the statements displayed in this file are the
certified ones.  Nothing is assumed: no theorem takes a cited result as a hypothesis.

The model is that of `DimRed/Support/Basic.lean`.  `DimRed.odo d N s₀ t` is the parallel
toppling odometer `v_t` of the initial sandpile `s₀` on the cube `C_N^{(d)}`, extended by
`0` off the cube; `DimRed.odoInf` is its terminal value `v_∞` in `ℕ∞`; `DimRed.inCube` and
`DimRed.inSimplex` are membership in the cube and in the sorted fundamental domain
`S_M^{(d)}`; `DimRed.nbrSum` and `DimRed.lap` are the neighbour sum and the Laplacian.

All of them reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
see `DimRed/Meta/AxiomsAudit.lean`.
-/

open LatticeProb DimRed

/-! ## The main results -/

/-- **Theorem 1.1(i)** (`the_theorem`), first display: dimensional reduction on the centre
slice, `v_t^{(d,N)}(x_{d-1}, 1) = v_t^{(d-1,N)}(x_{d-1})` for every `t ≥ 1`.  The certified
statement is `DimRed.Frozen.dimensional_reduction`, restated unchanged. -/
theorem DimRed.dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x := by
  exact DimRed.Frozen.dimensional_reduction N d hN hd t ht x hx

/-- **Theorem 1.1(i)** (`the_theorem`), second display: terminal dimensional reduction,
`v_∞^{(d,N)}(x_{d-1}, 2) = v_∞^{(d-1,N)}(x_{d-1})` for `x_{d-1} ≥ 2`.  The certified
statement is `DimRed.Frozen.terminal_dimensional_reduction`, restated unchanged. -/
theorem DimRed.terminal_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) N (Fin.snoc x 2) = odoInfUnif d N x := by
  exact DimRed.Frozen.terminal_dimensional_reduction N d hN hd x hx hx2

/-- **Theorem 1.1(ii)** (`the_theorem`): self-similarity for `t ≤ τ_j`, with the topple
time `τ_j` the first time some inner boundary site reaches height `j`.  The certified
statement is `DimRed.Frozen.self_similarity`, restated unchanged. -/
theorem DimRed.self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    odoUnif d N t x = odoUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  exact DimRed.Frozen.self_similarity N d hN hd j hj t ht x hx hxgt

/-- **Corollary 1.1(i)**: dimensional reduction of the terminal sandpile,
`s_∞^{(d,N)}(x_{d-1}, 1) = s_∞^{(d-1,N)}(x_{d-1}) + 2`.  The certified statement is
`DimRed.Frozen.sandpile_dimensional_reduction`, restated unchanged. -/
theorem DimRed.sandpile_dimensional_reduction (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    sandpInfUnif (d + 1) N (Fin.snoc x 1) = sandpInfUnif d N x + 2 := by
  exact DimRed.Frozen.sandpile_dimensional_reduction N d hN hd x hx hx2

/-- **Corollary 1.1(ii)**: self-similarity of the sandpile for `t ≤ τ_j`.  The certified
statement is `DimRed.Frozen.sandpile_self_similarity`, restated unchanged. -/
theorem DimRed.sandpile_self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    sandpUnif d N t x = sandpUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  exact DimRed.Frozen.sandpile_self_similarity N d hN hd j hj t ht x hx hxgt

/-! ## Proposition 4.1 -/

/-- **Proposition 4.1** (`base_dimension`), self-similarity clause: for `1 ≤ j ≤ M` and
`t ≤ τ_j`, `v_t^{(M)}(x) = v_t^{(j)}(x - (M - j))` for `x > M - j`.  The certified
statement is `DimRed.Frozen.base_dimension_consistency`, restated unchanged. -/
theorem DimRed.base_dimension_consistency (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ M) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d M x) (hxgt : ∀ i, (M : ℤ) - (j : ℤ) < x i) :
    odoUnif d (2 * M) t x = odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
  exact DimRed.Frozen.base_dimension_consistency d M hd hM j hj1 hj2 t ht x hx hxgt

/-- **Proposition 4.1** (`base_dimension`), weak facet compatibility: if
`v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1` then `v_{t+1}(x_i, 1, 1_j) = v_t(x_i, 1, 1_j)`.
The certified statement is `DimRed.Frozen.base_dimension_weak_compatibility`, restated
unchanged. -/
theorem DimRed.base_dimension_weak_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  exact DimRed.Frozen.base_dimension_weak_compatibility M i j hM t ht x hx2 hxs h

/-- **Proposition 4.1** (`base_dimension`), strong derivative clause:
`v_t(x_i, 1, 1_j) - v_t(x_i, 3, 1_j) ≤ 2` in the regular range.  The certified statement is
`DimRed.Frozen.base_dimension_strong_derivative`, restated unchanged. -/
theorem DimRed.base_dimension_strong_derivative (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2 := by
  exact DimRed.Frozen.base_dimension_strong_derivative M i j hM t x hx2 hxs hreg

/-- **Proposition 4.1** (`base_dimension`), strong facet compatibility: if
`v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1` then `v_{t+1}(x_i, 1, 1_j) = v_t(x_i, 1, 1_j)`
and `v_{t+1}(x_i, 2, 1_j) = v_t(x_i, 2, 1_j) + 1` in the regular range.  The certified
statement is `DimRed.Frozen.base_dimension_strong_compatibility`, restated unchanged. -/
theorem DimRed.base_dimension_strong_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞)))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) ∧
      odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 2 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1 := by
  exact DimRed.Frozen.base_dimension_strong_compatibility M i j hM t x hx2 hxs hreg h

/-- **Proposition 4.1** (`base_dimension`), strong topple control: for `t ≥ τ_{M-1}`,
`sup_{x ∈ S_M} (v_{t+2}(x) - v_t(x)) ≤ 1`.  The certified statement is
`DimRed.Frozen.base_dimension_strong_topple`, restated unchanged. -/
theorem DimRed.base_dimension_strong_topple (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    simplexMax d M (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1 := by
  exact DimRed.Frozen.base_dimension_strong_topple d M hd hM t ht

/-- **Lemma 2.1** (`pt_ind_lemma`), the parallel toppling recursion
`v_{t+1}(x) = ⌊(s_0(x) + ∑_{y ∼ x} v_t(y)) / 2d⌋` on the cube, for a nonnegative initial
sandpile bounded by `2(2d) - 1`.  The certified statement is
`DimRed.Frozen.pt_ind_lemma`, restated unchanged. -/
theorem DimRed.pt_ind_lemma (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x = (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ)) := by
  exact DimRed.Frozen.pt_ind_lemma d N hd s₀ hs0 hs1 t x hx

/-- **Lemma 2.2** (`parabolic_comparison`), the parabolic least action principle: the
odometer satisfies the parabolic inequality, and lies below every nonnegative function that
vanishes off the cube and satisfies it.  The certified statement is
`DimRed.Frozen.parabolic_comparison`, restated unchanged. -/
theorem DimRed.parabolic_comparison (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    (∀ (t : ℕ) (x : Site d), inCube d N x →
        (-(2 * (d : ℤ)) * odo d N s₀ (t + 1) x + nbrSum (odo d N s₀ t) x) + s₀ x
          ≤ 2 * (d : ℤ) - 1) ∧
      ∀ u : ℕ → Site d → ℤ, (∀ t y, 0 ≤ u t y) → (∀ t y, ¬ inCube d N y → u t y = 0) →
        (∀ (t : ℕ) (y : Site d), inCube d N y →
            (-(2 * (d : ℤ)) * u (t + 1) y + nbrSum (u t) y) + s₀ y ≤ 2 * (d : ℤ) - 1) →
        ∀ (t : ℕ) (y : Site d), odo d N s₀ t y ≤ u t y := by
  exact DimRed.Frozen.parabolic_comparison d N hd s₀ hs0 hs1

/-- **Lemma 2.3** (`symmetry_lemma`): for a symmetric initial sandpile the odometer is
invariant under every symmetry of the hypercube.  The certified statement is
`DimRed.Frozen.symmetry_lemma`, restated unchanged. -/
theorem DimRed.symmetry_lemma (d N : ℕ) (s₀ : Site d → ℤ) (hsym : IsSymmetricPile d N s₀)
    (t : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) :
    odo d N s₀ t (cubeSym d N π ε x) = odo d N s₀ t x := by
  exact DimRed.Frozen.symmetry_lemma d N s₀ hsym t π ε x

/-- **Lemma 2.4** (`general_difference_comparison`), the derivative comparison: a bound on
differences of the odometer along given steps that holds initially and on the boundary
persists at every later time.  The certified statement is
`DimRed.Frozen.general_difference_comparison`, restated unchanged. -/
theorem DimRed.general_difference_comparison (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    {n : ℕ} (w : Fin n → Site d) (g : Fin n → Site d → ℤ)
    (hg : ∀ k, SuperharmonicIn d M (g k)) (t₀ : ℕ)
    (hinit : ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) t₀ x - odo d (2 * M) (fun _ => c) t₀ (x + w k) - g k x ≤ 0)
    (hbdry : ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → (bdry M 0 x ∨ ∃ k, bdry M (w k) x) →
      ((∀ k, inCube d (2 * M) (x + w k) ∧
          nbrSum (odo d (2 * M) (fun _ => c) t) x
          - nbrSum (odo d (2 * M) (fun _ => c) t) (x + w k) - 2 * (d : ℤ) * g k x ≤ 0) ∨
       (∀ k, odo d (2 * M) (fun _ => c) (t + 1) x
          - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0))) :
    ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) (t + 1) x
        - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0 := by
  exact DimRed.Frozen.general_difference_comparison d M hd c hc0 hc1 w g hg t₀ hinit hbdry

/-- **Corollary 2.1** (`axis_monotonicity`), in the form of Babai and Gorodezky that the
paper cites: the odometer of a constant initial sandpile does not increase
along one step `e_i - ∑_{j ∈ J} e_j` with `#J ≤ 1` and `i < j`.  The certified statement is
`DimRed.Frozen.axis_monotonicity`, restated unchanged. -/
theorem DimRed.axis_monotonicity (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (_ht : 1 ≤ t) (x : Site d) (hx : inSimplex d M x)
    (i : Fin d) (J : Finset (Fin d)) (hJ : J.card ≤ 1) (hiJ : ∀ j ∈ J, i < j)
    (hmem : inSimplex d M (x + unit i - ∑ j ∈ J, unit j)) :
    odo d (2 * M) (fun _ => c) t (x + unit i - ∑ j ∈ J, unit j)
      ≤ odo d (2 * M) (fun _ => c) t x := by
  exact DimRed.Frozen.axis_monotonicity d M hd c hc0 hc1 t _ht x hx i J hJ hiJ hmem

/-- **Corollary 2.2** (`cor:derivative_bound`), the derivative bound: if the terminal
odometer at the corner is at most `k M`, then `v_t(x) - v_t(x + e_j) ≤ k x_j` on the sorted
domain.  The certified statement is `DimRed.Frozen.derivative_bound`, restated unchanged. -/
theorem DimRed.derivative_bound (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (k : ℕ) (hk : 1 ≤ k)
    (hcorner : odoInf d (2 * M) (fun _ => c) (cornerPoint d M) ≤ ((k * M : ℕ) : ℕ∞))
    (j : Fin d) (t : ℕ) (x : Site d) (hx : inSimplex d M x) :
    odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + unit j)
      ≤ (k : ℤ) * x j := by
  exact DimRed.Frozen.derivative_bound d M hd c hc0 hc1 k hk hcorner j t x hx

/-- **Lemma 2.5** (`topple_limit`), weak topple control: the largest increase of the
odometer over `j` steps on the sorted domain does not grow with time.  The certified
statement is `DimRed.Frozen.topple_limit`, restated unchanged. -/
theorem DimRed.topple_limit (d M : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d (2 * M) y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d (2 * M) y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (hsym : IsSymmetricPile d (2 * M) s₀) (t₀ t j : ℕ) (ht : t₀ ≤ t) :
    simplexMax d M (fun z => odo d (2 * M) s₀ (t + j) z - odo d (2 * M) s₀ t z) ≤
      simplexMax d M (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z) := by
  exact DimRed.Frozen.topple_limit d M hd s₀ hs0 hs1 hsym t₀ t j ht

/-- **Proposition 3.1**: on the cube of side `2`, with `s_0 ≡ 2d + (d_0 - 1)`, the terminal
odometer is `1` in dimension `d_0` but `2` in dimension `d_0 - 1`, so dimensional reduction
fails there.  The certified statement is
`DimRed.Frozen.no_reduction_at_critical_dimension`, restated unchanged. -/
theorem DimRed.no_reduction_at_critical_dimension (d₀ : ℕ) (hd₀ : 2 ≤ d₀) :
    (∀ x : Site d₀, inCube d₀ 2 x →
        odoInf d₀ 2 (fun _ => 2 * (d₀ : ℤ) + ((d₀ : ℤ) - 1)) x = 1) ∧
      (∀ x : Site (d₀ - 1), inCube (d₀ - 1) 2 x →
        odoInf (d₀ - 1) 2 (fun _ => 2 * ((d₀ - 1 : ℕ) : ℤ) + ((d₀ : ℤ) - 1)) x = 2) := by
  exact DimRed.Frozen.no_reduction_at_critical_dimension d₀ hd₀

/-- **Lemma 3.1**, the radial Laplacian on the cube of side `4`:
`Δ v_t(x) = (-d - x) v_t(x) + (d - x) v_t(x + 1) + x v_t(x - 1)` in the radial coordinate
`x`.  The certified statement is `DimRed.Frozen.radial_laplacian`, restated unchanged. -/
theorem DimRed.radial_laplacian (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    lap (odo d 4 (fun _ => c) t) (radial d k)
      = (-(d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d k)
        + ((d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d (k + 1))
        + (k : ℤ) * odo d 4 (fun _ => c) t (radial d (k - 1)) := by
  exact DimRed.Frozen.radial_laplacian d c t k hk

/-- **Proposition 3.2** (`prop:base_case`), the explicit odometer on the cube of side `4`
for `s_0 ≡ 2d + (d - 1)`: the firing block, and the ripple, which shifts the profile
outward by one site per step.  The certified statement is
`DimRed.Frozen.base_case`, restated unchanged. -/
theorem DimRed.base_case (d : ℕ) (hd : 1 ≤ d) (t : ℕ) :
    (∀ x : ℕ, x ≤ d →
        ((x : ℤ) ≤ blockEdge d (t + 1) →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
            = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) + 1) ∧
        (blockEdge d (t + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d t →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
            = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x))) ∧
      ∀ s : ℕ, s + 1 ≤ t → ∀ x : ℕ, t - s ≤ x → x ≤ d →
        (x : ℤ) ≤ blockEdge d s → blockEdge d (s + 1) < (x : ℤ) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (t - s))) := by
  exact DimRed.Frozen.base_case d hd t
