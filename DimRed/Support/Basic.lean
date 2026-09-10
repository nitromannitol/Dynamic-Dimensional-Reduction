/-
The vocabulary of the paper.

`dimred.tex:271-273` embeds the hypercube of side `N` into `ℤ^d` as
`{x - k : 1 ≤ x_i ≤ 2k}` when `N = 2k` and as `{x + 1 : |x_i| ≤ k}` when
`N = 2k + 1`; both are the box whose coordinates run from `1 - ⌊N/2⌋` to
`⌈N/2⌉`, which is how `inCube` is written here.

`dimred.tex:275-281` is the graph Laplacian with dissipating boundary
conditions, `Δ^{(d)} f(x) = -2d f(x) + ∑_{y ∼ x} f(y)`, where `f(y) := 0` for
`y ∉ C_N^{(d)}`.  Every function below is a function on all of `ℤ^d` which
vanishes off the hypercube, so the padding is automatic.

`dimred.tex:100-107` defines the parallel toppling odometer by
`v_0 ≡ 0`, `v_{t+1} = v_t + 1{s_t ≥ 2d}`, `s_{t+1} = s_t + Δ(v_{t+1} - v_t)`.
Here `odo` is defined by the equivalent closed recursion in which `s_t` is
replaced by `s₀ + Δ v_t`; the paper's two displays are `odo_succ_eq` and
`sandp_succ`.
-/
import LatticeProb.Site

namespace DimRed

open LatticeProb

variable {d : ℕ}

/-- The smallest coordinate of the hypercube of side `N`, `1 - ⌊N/2⌋`. -/
def loCoord (N : ℕ) : ℤ := 1 - (N / 2 : ℕ)

/-- `M = ⌈N/2⌉`, `dimred.tex:110`. -/
def sideHalf (N : ℕ) : ℕ := (N + 1) / 2

/-- The largest coordinate of the hypercube of side `N`, `M = ⌈N/2⌉`. -/
def hiCoord (N : ℕ) : ℤ := (sideHalf N : ℤ)

/-- `x` lies in the hypercube `C_N^{(d)}` of side length `N`. -/
def inCube (d N : ℕ) (x : Site d) : Prop := ∀ i : Fin d, loCoord N ≤ x i ∧ x i ≤ hiCoord N

instance (d N : ℕ) : DecidablePred (inCube d N) := fun _ => Fintype.decidableForallFintype

/-- `x` lies in the sorted fundamental domain
`S_M^{(d)} = {M ≥ x_1 ≥ ⋯ ≥ x_d ≥ 1}`. -/
def inSimplex (d M : ℕ) (x : Site d) : Prop :=
  (∀ i : Fin d, 1 ≤ x i ∧ x i ≤ (M : ℤ)) ∧ ∀ i j : Fin d, i ≤ j → x j ≤ x i

instance (d M : ℕ) : DecidablePred (inSimplex d M) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The hypercube `C_N^{(d)}`, as a finite set. -/
noncomputable def cube (d N : ℕ) : Finset (Site d) :=
  Finset.Icc (fun _ => loCoord N) (fun _ => hiCoord N)

/-- The sorted fundamental domain `S_M^{(d)}`, as a finite set. -/
noncomputable def simplex (d M : ℕ) : Finset (Site d) :=
  letI := Classical.decPred (inSimplex d M)
  (Finset.Icc (fun _ => (1 : ℤ)) (fun _ => (M : ℤ))).filter (inSimplex d M)

/-- The inner boundary `∂C_N^{(d)}`, the sites of the hypercube with a
neighbour outside it. -/
noncomputable def innerBoundary (d N : ℕ) : Finset (Site d) :=
  letI := Classical.decPred fun x : Site d =>
    ∃ i : Fin d, ¬ inCube d N (x + unit i) ∨ ¬ inCube d N (x - unit i)
  (cube d N).filter fun x => ∃ i : Fin d, ¬ inCube d N (x + unit i) ∨ ¬ inCube d N (x - unit i)

/-- `∑_{y ∼ x} u(y)`, the sum over the `2d` nearest neighbours of `x`. -/
def nbrSum (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- `Δ^{(d)} u(x) = -2d u(x) + ∑_{y ∼ x} u(y)`. -/
def lap (u : Site d → ℤ) (x : Site d) : ℤ :=
  -(2 * (d : ℤ)) * u x + nbrSum u x

/-- The parallel toppling odometer `v_t` of the initial sandpile `s₀` on
`C_N^{(d)}`, extended by zero off the hypercube. -/
def odo (d N : ℕ) (s₀ : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      if inCube d N x then
        odo d N s₀ t x + (if 2 * (d : ℤ) ≤ s₀ x + lap (odo d N s₀ t) x then 1 else 0)
      else 0

/-- The parallel toppling sandpile `s_t = s₀ + Δ v_t`. -/
def sandp (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ :=
  s₀ x + lap (odo d N s₀ t) x

/-- The odometer of the paper's initial condition `s_0^{(d)} ≡ 2d`. -/
def odoUnif (d N t : ℕ) (x : Site d) : ℤ := odo d N (fun _ => 2 * (d : ℤ)) t x

/-- The sandpile of the paper's initial condition `s_0^{(d)} ≡ 2d`. -/
def sandpUnif (d N t : ℕ) (x : Site d) : ℤ := sandp d N (fun _ => 2 * (d : ℤ)) t x

/-- `v_∞`, the terminal odometer, valued in `ℕ∞` so that a site which never
stops toppling has the value `⊤` rather than a junk integer. -/
noncomputable def odoInf (d N : ℕ) (s₀ : Site d → ℤ) (x : Site d) : ℕ∞ :=
  ⨆ t : ℕ, ((odo d N s₀ t x).toNat : ℕ∞)

/-- `v_∞` for the initial condition `s_0^{(d)} ≡ 2d`. -/
noncomputable def odoInfUnif (d N : ℕ) (x : Site d) : ℕ∞ :=
  odoInf d N (fun _ => 2 * (d : ℤ)) x

/-- `s_∞`, the terminal sandpile, for the initial condition `s_0^{(d)} ≡ 2d`. -/
noncomputable def sandpInfUnif (d N : ℕ) (x : Site d) : ℤ :=
  2 * (d : ℤ) + lap (fun y => ((odoInfUnif d N y).toNat : ℤ)) x

/-- `max_{z ∈ S_M^{(d)}} f(z)`; the value on an empty domain is `0`, and
`simplex_nonempty` shows the domain is nonempty when `1 ≤ M`. -/
noncomputable def simplexMax (d M : ℕ) (f : Site d → ℤ) : ℤ :=
  if h : (simplex d M).Nonempty then (simplex d M).sup' h f else 0

/-- `τ_j = min{t ≥ 1 : v_t^{(d,2j)}(x) ≥ j for all x ∈ ∂C_{2j}^{(d)}}`,
`dimred.tex:130-133`, valued in `ℕ∞` so that `⊤` records that no such time
exists. -/
noncomputable def toppleTime (d j : ℕ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) ''
    {n : ℕ | 1 ≤ n ∧ ∀ x ∈ innerBoundary d (2 * j), (j : ℤ) ≤ odoUnif d (2 * j) n x})

/-- The action on `ℤ^d` of a symmetry of the hypercube of side `N`: a permutation
of the coordinates followed by the reflections `x_i ↦ (lo + hi) - x_i`.  This is
the paper's `Aut_{C_d}` acting by matrix-vector multiplication followed by the
translation which preserves `C_N^{(d)}` (`dimred.tex:389-397`); `lo + hi` is `1`
for even `N` and `2` for odd `N`. -/
def cubeSym (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) : Site d :=
  fun i => if ε i then x (π i) else (loCoord N + hiCoord N) - x (π i)

/-- `s₀` is symmetric: `σ s₀ = s₀` for every symmetry `σ` of the hypercube. -/
def IsSymmetricPile (d N : ℕ) (s₀ : Site d → ℤ) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d),
    s₀ (cubeSym d N π ε x) = s₀ x

/-- The point `(2_k, 1_{d-k})` of the radial reparameterization of `S_2^{(d)}`,
`dimred.tex:724-726`. -/
def radial (d k : ℕ) : Site d := fun i => if (i : ℕ) < k then 2 else 1

/-- The point `(x_i, c, 1_j)` of `dimred.tex:918-943`: the `i` coordinates of
`x`, then `c`, then `j` coordinates equal to `1`. -/
def facetPoint {i : ℕ} (x : Fin i → ℤ) (c : ℤ) (j : ℕ) : Site (i + 1 + j) :=
  Fin.append (Fin.snoc x c) (fun _ : Fin j => (1 : ℤ))

/-- `⌈√n⌉`. -/
def ceilSqrt (n : ℕ) : ℕ := if n = 0 then 0 else Nat.sqrt (n - 1) + 1

/-- `t_d = ⌈√(d-1)⌉ + 1`, `dimred.tex:781-783`. -/
def tCrit (d : ℕ) : ℕ := ceilSqrt (d - 1) + 1

/-- The right edge `a_t` of the firing block, `dimred.tex:784-790`:
`a_1 = d`, `a_t = ⌊(d-1)/(t-1)⌋` for `t ≤ t_d` and `a_t = a_{t-1} - 1` after. -/
def blockEdge (d : ℕ) : ℕ → ℤ
  | 0 => (d : ℤ)
  | 1 => (d : ℤ)
  | (t + 2) =>
      if t + 2 ≤ tCrit d then ((d : ℤ) - 1) / ((t : ℤ) + 1) else blockEdge d (t + 1) - 1

/-- The point `(M, 1_{d-1})` of `dimred.tex:531`. -/
def cornerPoint (d M : ℕ) : Site d := fun i => if (i : ℕ) = 0 then (M : ℤ) else 1

/-- The dissipating boundary `B_w^{(disp)} S_M`, `dimred.tex:453-455`. -/
def dispBoundary (M : ℕ) (w x : Site d) : Prop := ∃ i : Fin d, (M : ℤ) ≤ (x + w) i

/-- The reflecting boundary `B_w^{(ref)} S_M`, `dimred.tex:457-459`. -/
def refBoundary (w x : Site d) : Prop := ∃ i : Fin d, (x + w) i ≤ 1

/-- The rotating boundary `B_w^{(rot)} S_M`, `dimred.tex:461-463`. -/
def rotBoundary (w x : Site d) : Prop := ∃ i j : Fin d, i < j ∧ (x + w) i ≤ (x + w) j

/-- `B_w`, the union of the three boundaries, `dimred.tex:465-467`. -/
def bdry (M : ℕ) (w x : Site d) : Prop :=
  dispBoundary M w x ∨ refBoundary w x ∨ rotBoundary w x

/-- `g` is superharmonic in the interior of `S_M^{(d)}`, the sites of the domain
all of whose nearest neighbours lie in the domain. -/
def SuperharmonicIn (d M : ℕ) (g : Site d → ℤ) : Prop :=
  ∀ x : Site d, inSimplex d M x →
    (∀ i : Fin d, inSimplex d M (x + unit i) ∧ inSimplex d M (x - unit i)) →
    nbrSum g x ≤ 2 * (d : ℤ) * g x

/-- The neighbour step of `x` that `cubeSym` carries to the step `e_i` of
`cubeSym x`. -/
def symStep {d : ℕ} (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d) : Site d :=
  if ε i then unit (π i) else -unit (π i)

end DimRed
