import Mathlib

/-!
# Theorem 1.1(ii) (`the_theorem`, clause 2): comparator challenge

Mathlib-only comparator challenge for Theorem 1.1(ii) (`the_theorem`, `dimred-corrected-arxiv.tex:109-133`)
of Bou-Rabee, *Dynamic dimensional reduction in the Abelian sandpile*: self-similarity of
the odometer up to the topple time `τ_j`.  The library statement is
`DimRed.Frozen.self_similarity`, restated in `DimRed/MainTheorems.lean` as
`DimRed.self_similarity`.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END`
rebuilds, from Mathlib primitives, every definition needed to read the theorem: the sites
and unit vectors of `ℤ^d`, the hypercube `C_N^{(d)}` and its inner boundary, the sorted
fundamental domain `S_M^{(d)}`, the neighbour sum and the Laplacian with dissipating
boundary conditions, the parallel toppling odometer and sandpile, their terminal values,
and the topple time `τ_j`.  It is a statement-level copy of the repository definitions
(see `DimRedAudit/README.md` for the provenance table) and is byte-identical in the four
challenges.  The sole intentional `sorry` is the proof of the final theorem.

## Presentation deltas

None: the theorem below is the statement of `DimRed.self_similarity` with every repository
name replaced by its vocabulary copy.  `τ_j` is `toppleTime d j`, an infimum in `ℕ∞`, so
`t ≤ τ_j` is an inequality there.  Vector inequalities and the subtraction of a scalar from
a vector are coordinatewise (`dimred-corrected-arxiv.tex:275`).
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
`dimred-corrected-arxiv.tex:733`. -/
def facetPoint {i : ℕ} (x : Fin i → ℤ) (c : ℤ) (j : ℕ) : Site (i + 1 + j) :=
  Fin.append (Fin.snoc x c) (fun _ : Fin j => (1 : ℤ))

end DimRed.StatementAudit
-- VOCABULARY-END

namespace DimRed.StatementAudit.SelfSimilarity

/-- **Theorem 1.1(ii)** (`the_theorem`, `dimred-corrected-arxiv.tex:122-133`): self-similarity, for all
`j < M`, `t ≤ τ_j` and `x ∈ S_M^{(d)}` with `x > M - j`,
`v_t^{(d,N)}(x) = v_t^{(d,2j)}(x - (M - j))`. -/
theorem self_similarity (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ) (ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    odoUnif d N t x = odoUnif d (2 * j) t (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  sorry

end DimRed.StatementAudit.SelfSimilarity
