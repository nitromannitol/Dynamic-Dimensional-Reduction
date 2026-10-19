import Mathlib

/-!
# Proposition 4.1 (`base_dimension`): comparator challenge

Mathlib-only comparator challenge for the five clauses of Proposition 4.1 (`base_dimension`,
`dimred-corrected-arxiv.tex:723-768`) of Bou-Rabee, *Dynamic dimensional reduction in the Abelian sandpile*:
self-similarity, weak facet compatibility, the strong derivative bound, strong facet
compatibility and strong topple control.  The library statements are
`DimRed.Frozen.base_dimension_consistency`, `..._weak_compatibility`,
`..._strong_derivative`, `..._strong_compatibility` and `..._strong_topple`, restated in
`DimRed/MainTheorems.lean`.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END`
rebuilds, from Mathlib primitives, every definition needed to read the clauses: the sites of
`ℤ^d`, the hypercube and its inner boundary, the sorted fundamental domain `S_M^{(d)}`, the
Laplacian, the parallel toppling odometer and sandpile, the terminal values, the topple time,
the facet point and the simplex maximum.  It is a statement-level copy of the repository
definitions (see `DimRedAudit/README.md` for the provenance table) and is byte-identical in the
four challenges.  The sole intentional `sorry`s are the proofs of the five clauses.
-/

-- VOCABULARY-BEGIN
namespace DimRed.StatementAudit

/-! ## 1. The lattice, the hypercube and the fundamental domain (`dimred-corrected-arxiv.tex:110-132`, `279`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector `e_i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- The smallest coordinate of the hypercube of side `N`, `1 - ⌊N/2⌋`. -/
def loCoord (N : ℕ) : ℤ := 1 - (N / 2 : ℕ)

/-- `M = ⌈N/2⌉`, `dimred-corrected-arxiv.tex:110`. -/
def sideHalf (N : ℕ) : ℕ := (N + 1) / 2

/-- The largest coordinate of the hypercube of side `N`, `M = ⌈N/2⌉`. -/
def hiCoord (N : ℕ) : ℤ := (sideHalf N : ℤ)

/-- `x` lies in the hypercube `C_N^{(d)}` of side length `N`: `dimred-corrected-arxiv.tex:279` embeds it
as `{x - k : 1 ≤ x_i ≤ 2k}` when `N = 2k` and as `{x + 1 : |x_i| ≤ k}` when `N = 2k + 1`,
the box whose coordinates run from `1 - ⌊N/2⌋` to `⌈N/2⌉`. -/
def inCube (d N : ℕ) (x : Site d) : Prop := ∀ i : Fin d, loCoord N ≤ x i ∧ x i ≤ hiCoord N

instance (d N : ℕ) : DecidablePred (inCube d N) := fun _ => Fintype.decidableForallFintype

/-- `x` lies in the sorted fundamental domain
`S_M^{(d)} = {M ≥ x_1 ≥ ⋯ ≥ x_d ≥ 1}`, `dimred-corrected-arxiv.tex:110-111`. -/
def inSimplex (d M : ℕ) (x : Site d) : Prop :=
  (∀ i : Fin d, 1 ≤ x i ∧ x i ≤ (M : ℤ)) ∧ ∀ i j : Fin d, i ≤ j → x j ≤ x i

/-- The hypercube `C_N^{(d)}`, as a finite set. -/
noncomputable def cube (d N : ℕ) : Finset (Site d) :=
  Finset.Icc (fun _ => loCoord N) (fun _ => hiCoord N)

/-- The inner boundary `∂C_N^{(d)}`, the sites of the hypercube with a nearest neighbour
outside it, `dimred-corrected-arxiv.tex:132`. -/
noncomputable def innerBoundary (d N : ℕ) : Finset (Site d) :=
  letI := Classical.decPred fun x : Site d =>
    ∃ i : Fin d, ¬ inCube d N (x + unit i) ∨ ¬ inCube d N (x - unit i)
  (cube d N).filter fun x => ∃ i : Fin d, ¬ inCube d N (x + unit i) ∨ ¬ inCube d N (x - unit i)

/-! ## 2. Parallel toppling (`dimred-corrected-arxiv.tex:38`, `93-97`, `278-284`) -/

/-- `∑_{y ∼ x} u(y)`, the sum over the `2d` nearest neighbours of `x`. -/
def nbrSum {d : ℕ} (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The graph Laplacian `Δ^{(d)} u(x) = -2d u(x) + ∑_{y ∼ x} u(y)`, `dimred-corrected-arxiv.tex:280-286`.
Every function it is applied to below vanishes off the hypercube, which is the paper's
padding `f(y) := 0` for `y ∉ C_N^{(d)}` (dissipating boundary conditions). -/
def lap {d : ℕ} (u : Site d → ℤ) (x : Site d) : ℤ :=
  -(2 * (d : ℤ)) * u x + nbrSum u x

/-- The parallel toppling odometer `v_t` of the initial sandpile `s₀` on `C_N^{(d)}`,
extended by zero off the hypercube.  `dimred-corrected-arxiv.tex:93-97` defines it by `v_0 ≡ 0`,
`v_{t+1} = v_t + 1{s_t ≥ 2d}`, `s_{t+1} = s_t + Δ(v_{t+1} - v_t)`; this is the equivalent
closed recursion in which `s_t` is replaced by `s₀ + Δ v_t`. -/
def odo (d N : ℕ) (s₀ : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      if inCube d N x then
        odo d N s₀ t x + (if 2 * (d : ℤ) ≤ s₀ x + lap (odo d N s₀ t) x then 1 else 0)
      else 0

/-- The parallel toppling sandpile `s_t = s₀ + Δ v_t`. -/
def sandp (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ :=
  s₀ x + lap (odo d N s₀ t) x

/-- The odometer `v_t^{(d,N)}` of the paper's initial condition `s_0^{(d)} ≡ 2d`
(`dimred-corrected-arxiv.tex:38`). -/
def odoUnif (d N t : ℕ) (x : Site d) : ℤ := odo d N (fun _ => 2 * (d : ℤ)) t x

/-- The sandpile `s_t^{(d,N)}` of the paper's initial condition `s_0^{(d)} ≡ 2d`. -/
def sandpUnif (d N t : ℕ) (x : Site d) : ℤ := sandp d N (fun _ => 2 * (d : ℤ)) t x

/-- `v_∞`, the terminal odometer, valued in `ℕ∞` so that a site which never stops toppling
has the value `⊤` rather than a junk integer. -/
noncomputable def odoInf (d N : ℕ) (s₀ : Site d → ℤ) (x : Site d) : ℕ∞ :=
  ⨆ t : ℕ, ((odo d N s₀ t x).toNat : ℕ∞)

/-- `v_∞^{(d,N)}` for the initial condition `s_0^{(d)} ≡ 2d`. -/
noncomputable def odoInfUnif (d N : ℕ) (x : Site d) : ℕ∞ :=
  odoInf d N (fun _ => 2 * (d : ℤ)) x

/-- `s_∞^{(d,N)} = 2d + Δ v_∞`, the terminal sandpile for the initial condition
`s_0^{(d)} ≡ 2d`. -/
noncomputable def sandpInfUnif (d N : ℕ) (x : Site d) : ℤ :=
  2 * (d : ℤ) + lap (fun y => ((odoInfUnif d N y).toNat : ℤ)) x

/-- `τ_j = min{t ≥ 1 : v_t^{(d,2j)}(x) ≥ j for some x ∈ ∂C_{2j}^{(d)}}`,
`dimred-corrected-arxiv.tex:128-131`, valued in `ℕ∞` so that `⊤` records that no such time exists. -/
noncomputable def toppleTime (d j : ℕ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) ''
    {n : ℕ | 1 ≤ n ∧ ∃ x ∈ innerBoundary d (2 * j), (j : ℤ) ≤ odoUnif d (2 * j) n x})

/-- The sorted fundamental domain `S_M^{(d)}`, as a finite set. -/
noncomputable def simplex (d M : ℕ) : Finset (Site d) :=
  letI := Classical.decPred (inSimplex d M)
  (Finset.Icc (fun _ => (1 : ℤ)) (fun _ => (M : ℤ))).filter (inSimplex d M)

/-- `sup_{x ∈ S_M} f(x)`, the maximum of `f` over the finite domain `S_M` (`0` if empty). -/
noncomputable def simplexMax (d M : ℕ) (f : Site d → ℤ) : ℤ :=
  if h : (simplex d M).Nonempty then (simplex d M).sup' h f else 0

/-- The facet point `(x, c, 1_j)`, the paper's `(\mathbf{x}_i, c, \mathbf{1}_j)`,
`dimred-corrected-arxiv.tex:726`. -/
def facetPoint {i : ℕ} (x : Fin i → ℤ) (c : ℤ) (j : ℕ) : Site (i + 1 + j) :=
  Fin.append (Fin.snoc x c) (fun _ : Fin j => (1 : ℤ))

end DimRed.StatementAudit
-- VOCABULARY-END

namespace DimRed.StatementAudit.Regularity

/-- **Proposition 4.1** (`base_dimension`), self-similarity clause (`dimred-corrected-arxiv.tex:727-729`):
for `M ≥ 2`, `1 ≤ j ≤ M`, `t ≤ τ_j` and `x ∈ S_M` with `x > M - j`,
`v_t^{(M)}(x) = v_t^{(j)}(x - (M - j))`. -/
theorem base_dimension_consistency (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ M) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d M x) (hxgt : ∀ i, (M : ℤ) - (j : ℤ) < x i) :
    odoUnif d (2 * M) t x = odoUnif d (2 * j) t (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
  sorry

/-- **Proposition 4.1** (`base_dimension`), weak facet compatibility (`dimred-corrected-arxiv.tex:731-738`):
if `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1` then `v_{t+1}(x_i, 1, 1_j) = v_t(x_i, 1, 1_j)`. -/
theorem base_dimension_weak_compatibility (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (ht : 1 ≤ t) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (h : odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
        = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 2 j) + 1) :
    odoUnif (i + 1 + j) (2 * M) (t + 1) (facetPoint x 1 j)
      = odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j) := by
  sorry

/-- **Proposition 4.1** (`base_dimension`), strong derivative bound (`dimred-corrected-arxiv.tex:743-745`):
for `x_i ≥ 2`, `j ≥ 0` and the regime `t < τ_M` or `i ≥ 1, t ≥ τ_M`,
`v_t(x_i, 1, 1_j) - v_t(x_i, 3, 1_j) ≤ 2`. -/
theorem base_dimension_strong_derivative (M i j : ℕ) (hM : 2 ≤ M)
    (t : ℕ) (x : Fin i → ℤ) (hx2 : ∀ a, 2 ≤ x a)
    (hxs : inSimplex (i + 1 + j) M (facetPoint x 1 j))
    (hreg : (t : ℕ∞) < toppleTime (i + 1 + j) M ∨
      (1 ≤ i ∧ toppleTime (i + 1 + j) M ≤ (t : ℕ∞))) :
    odoUnif (i + 1 + j) (2 * M) t (facetPoint x 1 j)
      - odoUnif (i + 1 + j) (2 * M) t (facetPoint x 3 j) ≤ 2 := by
  sorry

/-- **Proposition 4.1** (`base_dimension`), strong facet compatibility (`dimred-corrected-arxiv.tex:747-755`):
under the derivative bound's hypotheses and the gap
`v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1`, the first point stays and the second topples. -/
theorem base_dimension_strong_compatibility (M i j : ℕ) (hM : 2 ≤ M)
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
  sorry

/-- **Proposition 4.1** (`base_dimension`), strong topple control (`dimred-corrected-arxiv.tex:761-763`):
for all `t ≥ τ_{M-1}`, `sup_{x ∈ S_M}(v_{t+2}(x) - v_t(x)) ≤ 1`. -/
theorem base_dimension_strong_topple (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (t : ℕ) (ht : toppleTime d (M - 1) ≤ (t : ℕ∞)) :
    simplexMax d M (fun x => odoUnif d (2 * M) (t + 2) x - odoUnif d (2 * M) t x) ≤ 1 := by
  sorry

end DimRed.StatementAudit.Regularity
