# Correspondence between the paper and the formalization

`paper/dimred.tex` is the contract.  This file records, for every choice that a
reader might otherwise have to reconstruct, how a statement of the paper became
a Lean statement.

## The vocabulary

| paper | Lean | notes |
|---|---|---|
| `C_N^{(d)}`, `dimred.tex:271-273` | `DimRed.inCube d N` | the paper embeds the cube two ways depending on the parity of `N`; both are the box with coordinates in `[1 - ⌊N/2⌋, ⌈N/2⌉]`, which is the single definition used here |
| `M = ⌈N/2⌉` | `DimRed.hiCoord N` | |
| `S_M^{(d)}`, `dimred.tex:363-366` | `DimRed.inSimplex d M`, `DimRed.simplex d M` | the predicate is decidable; the `Finset` is used where the paper takes a maximum over the domain |
| `∂C_N^{(d)}`, `dimred.tex:134-136` | `DimRed.innerBoundary d N` | |
| `Δ^{(d)}`, `dimred.tex:275-281` | `DimRed.lap` | every function in the development vanishes off the cube, so the paper's padding `f(y) := 0` for `y ∉ C` is automatic |
| `∑_{y ∼ x}` | `DimRed.nbrSum` | the sum over the `2d` neighbours, direction by direction |
| `v_t`, `dimred.tex:100-107` | `DimRed.odo d N s₀ t` | |
| `s_t`, `dimred.tex:100-107` | `DimRed.sandp d N s₀ t` | |
| `v_t^{(d,N)}` for `s_0 ≡ 2d` | `DimRed.odoUnif d N t` | |
| `s_t^{(d,N)}` for `s_0 ≡ 2d` | `DimRed.sandpUnif d N t` | |
| `v_∞` | `DimRed.odoInf` | valued in `ℕ∞`; see "junk values" below |
| `τ_j`, `dimred.tex:130-133` | `DimRed.toppleTime d j` | valued in `ℕ∞`; see "junk values" below |
| `max_{z ∈ S_M}` | `DimRed.simplexMax` | |

## How the odometer is defined

The paper defines the pair `(v_t, s_t)` by the mutual recursion
`v_0 ≡ 0`, `v_{t+1} = v_t + 1{s_t ≥ 2d}`, `s_{t+1} = s_t + Δ(v_{t+1} - v_t)`
(`dimred.tex:100-107`).  Since `s_t = s_0 + Δ v_t` for every `t`, `DimRed.odo`
is defined by the single recursion in which `s_t` is written out, and
`DimRed.sandp` by the closed form `s₀ + Δ v_t`.  The paper's two displays are
then theorems, `DimRed.odo_succ_eq` and `DimRed.sandp_succ`, so nothing is
assumed by the choice.

## The symmetrized odometer

Sections 2.5 onward of the paper work with the symmetrized odometer `v^S` on
`S_M^{(d)}` with reflecting boundary conditions.  Lemma 2.3 (`symmetry_lemma`)
shows `v^S = v` on `S_M^{(d)}`, and the paper then says "Henceforth, we
consider `v_t^S` in `S_M^{(d)}` and drop all `S` superscripts".  Every frozen
statement here is therefore written with the cube odometer `DimRed.odo`
restricted to `S_M^{(d)}`, which is the same function.  No separate
symmetrized Laplacian is defined.

## Junk values

- `v_∞` is `⨆ t, (v_t x).toNat` in `ℕ∞`.  A site that never stops toppling has
  the value `⊤`, not a junk integer.  That the value is finite is a theorem of
  the development, not an assumption.
- `τ_j` is an `sInf` in `ℕ∞`, so a `j` for which no such time exists gives `⊤`
  and the hypothesis `t ≤ τ_j` of Theorem 1.1(ii) is then vacuously satisfied
  for every `t`, that is, the statement is strengthened rather than trivialized.
- `simplexMax d M f` is `0` on an empty domain; `simplex_nonempty` shows the
  domain is nonempty when `1 ≤ M`.
- Integer division `a / b` on `ℤ` is floor division for `b > 0`, so the paper's
  `⌊·/2d⌋` is written directly as `· / (2 * d)`.

## Hypotheses the development does NOT carry

`lem-symmetry` carries only the symmetry of the initial sandpile
(`dimred.tex:400-402`) and not the bound `0 ≤ s₀ ≤ 2(2d) - 1`, which its proof
does not use.  The statement is therefore stronger than the paper's.

## Nodes carrying cited inputs

None so far.  The paper cites Babai-Gorodezky for the attribution of Corollary
2.1 but proves it, and cites the comparison principle only in a remark.

## Hypotheses the paper leaves implicit

| node | added hypothesis | why |
|---|---|---|
| `lem-topple-limit` | `IsSymmetricPile d (2M) s₀` | version 2.  The first transcription carried only the bound of `dimred.tex:286-288` and omitted the standing hypothesis of `dimred.tex:400-402`, that the initial sandpile is symmetric, which is in force from Section 2.4 onward and is what makes a maximum over the fundamental domain a maximum over the whole hypercube.  Without it the statement is not the paper's |
| `lem-pt-ind`, `lem-parabolic-comparison`, `lem-topple-limit` | the bounds on `s₀` are hypotheses only ON the hypercube | version 3.  `dimred.tex:286-288` constrains the initial sandpile on `C`, not on all of `ℤ^d`; the odometer never reads `s₀` off the cube, so the restricted hypothesis is the paper's and gives the stronger statement |
| `lem-pt-ind` | `0 ≤ s₀` | `dimred.tex:286-288` assumes only `s_0 ≤ 2(2d) - 1`; the identity fails for a negative initial sandpile, for instance `s_0 ≡ -1`, where `v_t ≡ 0` but `⌊-1/2d⌋ = -1`.  Nonnegativity is part of what "sandpile" means in the paper (a number of chips) and is recorded in the errata |
