# Dynamic dimensional reduction in the Abelian sandpile

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, *Dynamic dimensional reduction in the Abelian sandpile*,
> Communications in Mathematical Physics 390 (2022), 933–958; arXiv:2009.05968.

The formalized text is a corrected edition of the arXiv source (v2), in
[`paper/corrected-arxiv/`](paper/corrected-arxiv/). The main results, Theorem 1.1 and
Corollary 1.1, are stated as published; in Theorem 1.1(ii) the hitting time `τ_j` is the first
time some inner boundary site has toppled `j` times, the quantifier the published definition
leaves unstated. The other changes are surgical corrections of lemmas, corollaries, two
propositions (3.2 and 4.1), definitions and proofs; each is listed below and in the section "Corrections to
the published version" of the corrected edition. The unmodified arXiv source is
[`paper/dimred-arxiv.tex`](paper/dimred-arxiv.tex).

[![CI](https://github.com/nitromannitol/Dynamic-Dimensional-Reduction/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Dynamic-Dimensional-Reduction/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Dynamic-Dimensional-Reduction/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Dynamic-Dimensional-Reduction/actions/workflows/comparator.yml)

## What is proved

Start with `2d` chips at every site of the cube `C_N^{(d)} ⊂ ℤ^d` and topple in parallel: at
each step every site with at least `2d` chips sends one chip to each neighbour, and chips
leaving the cube are lost. The odometer `v_t^{(d,N)}(x)` counts the topplings at `x` up to
time `t`. On the sorted fundamental domain `S_M^{(d)} = {M ≥ x_1 ≥ ⋯ ≥ x_d ≥ 1}`,
`M = ⌈N/2⌉`, Theorem 1.1 says that the centre slice of the `d`-dimensional process is the
`(d−1)`-dimensional process at every time, that the terminal odometers agree one layer further
in, and that cubes of different sizes agree near their corners up to the first time a boundary
site has toppled `j` times. Corollary 1.1 gives the same statements for the sandpile. The proof
is one induction over dimension, side length and time, carrying the regularity estimates of
Proposition 4.1.

Every result is stated in [`DimRed/MainTheorems.lean`](DimRed/MainTheorems.lean).

| Paper | Lean | Relation to the published statement |
|---|---|---|
| Theorem 1.1(i), both displays | `DimRed.dimensional_reduction`, `DimRed.terminal_dimensional_reduction` | as published |
| Theorem 1.1(ii) | `DimRed.self_similarity` | as published, with `τ_j` the first time some inner boundary site has toppled `j` times (C01) |
| Corollary 1.1 | `DimRed.sandpile_dimensional_reduction`, `DimRed.sandpile_self_similarity` | as published |
| Lemma 2.1 | `DimRed.pt_ind_lemma` | corrected (C02) |
| Lemma 2.2 | `DimRed.parabolic_comparison` | as published |
| Lemma 2.3 | `DimRed.symmetry_lemma` | corrected definition of the process $v^{\mathcal S}$ (C04) |
| Lemma 2.4 | `DimRed.general_difference_comparison` | corrected (C06) |
| Corollary 2.1 | `DimRed.axis_monotonicity` | corrected: elementary moves (C08) |
| Corollary 2.2, Lemma 2.5 | `DimRed.derivative_bound`, `DimRed.topple_limit` | as published |
| Proposition 3.1, Lemma 3.1 | `DimRed.no_reduction_at_critical_dimension`, `DimRed.radial_laplacian` | as published |
| Proposition 3.2 | `DimRed.base_case` | corrected ripple clause (C12, C13) |
| Proposition 4.1, five clauses | `DimRed.base_dimension_consistency`, `DimRed.base_dimension_weak_compatibility`, `DimRed.base_dimension_strong_derivative`, `DimRed.base_dimension_strong_compatibility`, `DimRed.base_dimension_strong_topple` | weak facet (C15), strong derivative (C16) and strong facet (C17) corrected |
| Lemma 4.1 (a remark of the published paper) | `DimRed.one_terminal_profile`, `DimRed.one_terminal_derivative` | proved here; the published paper cites it from the literature |
| Lemma 5.1 (new) | `DimRed.strict_head_facet` | used in the proof of Proposition 4.1 |

Nothing from the literature is assumed.

### Corrections to the published version

Each change from arXiv v2 is listed with the published text, the corrected text and the reason;
"Where" gives the line in [`paper/dimred-arxiv.tex`](paper/dimred-arxiv.tex). Changes marked
"proof only" leave the statement unchanged.

| Change | Where | Published | Corrected | Reason |
|---|---|---|---|---|
| C01 | Definition of $\tau_j$ in Theorem 1.1(ii) (line 128) | $\tau_{j} := \min\{ t \geq 1: v_t^{(d,2 j)}(\mathbf{x}) \geq j \text{ for } \mathbf{x} \in \partial \mathcal{C}^{(d)}_{2 j} \}$ | Same, with "for some $\mathbf{x}$", and $\min\varnothing := +\infty$ | The published quantifier is unstated; the discussion after the statements reads it as "a boundary site". |
| C02 | Lemma 2.1, point formula (line 292) | $v_{t+1}(x) = \lfloor (s_0(x) + \sum_{y \sim x} v_t(y))/2d \rfloor$ | $v_{t+1}(x) = \max\{0, \lfloor (s_0(x) + \sum_{y \sim x} v_t(y))/2d \rfloor\}$ | Signed initial values can make the untruncated formula negative. |
| C03 | Proof of Lemma 2.2, parabolic least action (lines 317–333); proof only | The proof identifies $v$ with the right-hand side $w$ and concludes by minimality of $w$ | The proof shows that $v$ is admissible and compares it with every nonnegative competitor, by induction on time | The published proof does not treat the zero truncation; the corrected comparison covers all nonnegative competitors, including arbitrary initial values. |
| C04 | Definition of the process $v^{\mathcal S}$ of Lemma 2.3 on the sorted fundamental domain (lines 369–404) | $v_{t+1}^{\mathcal S}(x) = \lfloor (s_0(x) + \sum_{y \overset{\mathcal S}{\sim} x} v_t^{\mathcal S}(y))/2d \rfloor$, with the sum over the set $\{\sigma_y y : y \sim x\}$ | $v_{t+1}^{\mathcal S}(x) = v_t^{\mathcal S}(x) + \mathbf{1}\{ s_0(x) + R v_t^{\mathcal S}(x) - 2d\, v_t^{\mathcal S}(x) \geq 2d \}$, where $R u(x) = \sum_{i=1}^d (\widetilde u(x+e_i) + \widetilde u(x-e_i))$ | The published sum drops repeated reflected neighbours, its chain $M = x_{l_0} = x_{r_0} < \cdots < x_{l_n} = x_{r_n} = 1$ has reversed inequalities, and its floor update fails for initial piles outside $[0,4d-1]$; the corrected sum runs over the $2d$ lattice neighbours with multiplicity and agrees with the published block-index formula (lines 391–404) when $0 \le s_0 \le 4d-1$. |
| C05 | Proof of Lemma 2.3, symmetry (lines 419–429); proof only | Induction proving symmetry of $v_t$ | Invariance under the cube symmetries by induction on time, then identification of the restriction of $v_t$ to $\mathcal S$ with $v_t^{\mathcal S}$ for symmetric initial piles of every height | The published proof gives only symmetry and does not identify $v^{\mathcal S}$. |
| C06 | Statement of Lemma 2.4 (line 481) | $\sup_{j} ( \sum_{y \sim x} v_t(y) - \sum_{y' \sim (x+w_j)} v_t(y') - 2d\, g_j(x) ) \leq 0$ | The same, with the first boundary alternative also requiring $x+w_j \in \mathcal C_N^{(d)}$ for every $j$ | The published statement fails for $d=1$, $N=4$, $s_0 \equiv 2$, $w=2$, $g \equiv 2$, $t_0=0$, at $t=3$ and $x=1$. |
| C07 | Proof of Lemma 2.4 (lines 494–508); proof only | Induction using a floor estimate and the superharmonicity of $g_j$ | Induction splitting each difference into strict and equality cases, with the boundary handled by the two alternatives | The strict and equality split covers every constant integer height. |
| C08 | Statement of Corollary 2.1, axis monotonicity (lines 514–526) | Mixed moves for index sets $\mathcal I$ and $\mathcal J$ of arbitrary size, with $i_n < j_1$ | Elementary moves: $1 \leq i \leq d$ and $\mathcal J = \varnothing$ or $\mathcal J = \{j\}$ with $i < j \leq d$ | The published statement is false when $\lvert\mathcal J\rvert > \lvert\mathcal I\rvert$, for example for $d=3$, $N=8$, $s_0 \equiv 8$, $t=8$, $\mathcal I=\{1\}$, $\mathcal J=\{2,3\}$; the proofs use only the elementary moves. |
| C09 | Proof of Corollary 2.1 (lines 529–530); proof only | No proof is given | Induction on time for the two families of elementary comparisons, pairing at equality the $2d$ lattice neighbours with multiplicity, by reflection or by coordinate interchange | Elementary axis moves need a direct threshold proof. |
| C10 | Proof of Corollary 2.2, derivative bound (lines 540–663); proof only | Case analysis through the index sets $\mathbf I^{(M,d)}(x)$ | Terminal-corner bound, axis monotonicity and symmetry on the top faces, and direct firing comparisons at the boundaries, for all constant integer heights | The published case analysis depends on the index algorithm that the corrected definition of $v^{\mathcal S}$ replaces. |
| C11 | Proof of Lemma 2.5, weak topple control (lines 679–692); proof only | Induction bounding $v_{t+j}(x) - v_t(x)$ by the floor update and the maximum over $\mathcal S$ | Contraction of the odometer rule, using cube symmetry and the nonempty maximum $C$ | The unrestricted floor argument is replaced by a contraction argument. |
| C12 | Definition of $a_t$, before Proposition 3.2 (line 779) | $a_1 = d$ | $a_0 = a_1 = d$ | Gives the first ripple window a left endpoint; no firing assertion is added at time zero. |
| C13 | Ripple clause of Proposition 3.2 (lines 798–800) | For each $t' < t$ and $a_{t'-1} \geq x > a_{t'}$: $v_{t}(x) = v_{t-1}(x-1)$ | For each $1 \leq t' < t \leq t'+x$ and $a_{t'-1} \geq x > a_{t'}$: $v_t(x) = v_{t'}(x-(t-t'))$ | The published clause is false (for example $d=2$, $s_0 \equiv 5$, $t'=2$, $x=2$, $t=6$); the shifted index must be nonnegative. |
| C14 | Proof of Proposition 3.2 (lines 816–896); proof only | Induction with the affine function $g(x) = (d-1) - tx$ and the ripple step | Keeps the block-edge term $-(d-x)$, uses the radial Laplacian, and proves the ripple identity by induction on $k=t-t'$ in the three cases $x-k<a_{t'}$, $x-k=a_{t'}$ and $x-k>a_{t'}$ | The published induction omits the block-edge term and these three cases, and states the affine monotonicity in the wrong direction. |
| C15 | Weak facet compatibility, Proposition 4.1 (line 924) | $v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) = v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j)$ | $v_{t+1}^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) = v_t^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j)$ | The published equation is a tautology; the corrected no-fire conclusion is the one the induction uses. |
| C16 | Strong facet compatibility, Proposition 4.1 (lines 927–930) | For $\mathbf{x}_i \geq 2$, $j \geq 0$, $i < d$ and the two time regimes: $v_t^{(M)}(\mathbf{x}) - v_t^{(M)}(\mathbf{x}+2e_{i+1}) \leq 2$ | For $i, j \geq 0$ with $i+1+j = d$ and $p = (\mathbf{x}_i, 1, \mathbf{1}_j)$ with $\mathbf{x}_i \geq 2$: $v_t^{(M)}(p) - v_t^{(M)}(p+2e_{i+1}) \leq 2$ in the same regimes | The published point is unbound; read broadly, the constant-two bound is false. |
| C17 | Strong compatibility equation, Proposition 4.1 (line 935) | $v_t^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) = v_t^{(M)}(\mathbf{x}_i, 2, \mathbf{1}) + 1$ | $v_t^{(M)}(\mathbf{x}_i, 1, \mathbf{1}_j) = v_t^{(M)}(\mathbf{x}_i, 2, \mathbf{1}_j) + 1$ | The tail subscript is missing. |
| C18 | Proof of Proposition 4.1 for $d \geq 2$, strong facet compatibility (lines 1262–1318); proof only | Derivation of the compatibility from the two-step bound $v_t(\mathbf{x}_{i-1}, 1, \mathbf{1}_j) - v_t(\mathbf{x}_{i-1}, 3, \mathbf{1}_j) \leq 2$ and a comparison of Laplacians | Joint induction in lexicographic order of dimension, side length and time; the case $i \geq 1$ is covered by Lemma 5.1 at every time, and the case $i=0$ (the point $\mathbf 1$) by comparing the neighbour sum of $\mathbf 1+e_k$ at time $t$ with that of $\mathbf 1$ at time $t-1$, using the two-step bound for $t<\tau_M$, the compatibility conclusions at earlier times and the assertion $L_t$ of Lemma 5.1's proof | The published derivation of the compatibility from the two-step bound is false, so the cases $i \geq 1$ and $i=0$ are treated separately. |
| C19 | Proof of Proposition 4.1 for $d \geq 2$, early times (lines 1319–1333); proof only | Bound stated for all $d \leq i \leq 1$, and a two-step estimate | Bound stated for all $1 \leq k \leq d$, with the two-step estimate counting each boundary neighbour with its multiplicity; the restriction $t < \tau_M$ is kept | The published index range is empty, and the estimate omits some boundary neighbours counted with multiplicity. |
| C20 | Proof of Proposition 4.1 for $d \geq 2$, later times (lines 1334–1362); proof only | Full-domain Case 2 estimate, the dissipating boundary shrunk to $\mathcal B^{(disp)}$, and a contradiction at the reflecting point | Full-domain estimate and the shrinking to $\mathcal B^{(disp)}$ withdrawn; the conclusions of Lemma 5.1, and with them those for $i \geq 1$, stated at every time; at $\mathbf 1$ (all coordinates one) only the fact that $\mathbf 1$ does not topple when $v_t(\mathbf 1)=v_t(\mathbf 1+e_k)+1$ is kept | The published full-domain estimate is false. |
| C21 | One-dimensional terminal profile, proof of Proposition 4.1 for $d=1$ (lines 1105–1110) | Unlabelled remark: $v_\infty(x) = \frac12(M(M+1)-x(x-1))$ and $v_\infty(x)-v_\infty(x+1) = x$ | Labelled lemma for $1 \leq x \leq M$ with $v_\infty(M+1) = 0$, and its proof | The profile is correct but unlabelled, and the difference omits the dissipating endpoint $x=M$. |
| C22 | Label on Corollary 1.1 (line 143) | Unlabelled | Labelled; statement unchanged | A label is needed for citation. |
| C23 | Label on the no-reduction proposition in Section 3 (line 706) | Unlabelled | Labelled; statement unchanged | A label is needed for citation. |
| C24 | Label on the radial Laplacian lemma in Section 3 (line 728) | Unlabelled | Labelled; statement unchanged | A label is needed for citation. |
| C25 | Proof of the radial Laplacian lemma (lines 735–768); proof only | Laplacian written through the index sets $\mathbf I^{(2,d)}(\mathbf x)$ | Exact count of the radial neighbours with multiplicities: $\Delta v_t(x) = -2d\, v_t(x) + x\, v_t(x-1) + (d-x)(v_t(x)+v_t(x+1))$, with zero endpoint coefficients | The published proof uses the index algorithm that the corrected definitions remove. |

## Standing assumptions and scope

- The cube of side `N` is the box `[1 − ⌊N/2⌋, ⌈N/2⌉]^d`, the paper's embedding for both
  parities; outside it every function is `0` (dissipating boundary).
- The odometer is `v_0 = 0`, `v_{t+1} = v_t + 1{s_0 + Δv_t ≥ 2d}`, and the sandpile is
  `s_t = s_0 + Δv_t`. In Theorem 1.1, Corollary 1.1 and Proposition 4.1 the initial condition
  in dimension `d` is `s_0 ≡ 2d`. The lemmas of Section 2 are stated for integer initial piles
  that are bounded by `4d − 1`, symmetric, or constant, as each lemma requires. Section 3 uses
  `s_0 ≡ 2d + (d − 1)` (and `2d + (d_0 − 1)`).
- `v_∞` is the supremum of `v_t` in `ℕ∞`; it is finite (`DimRed.terminal_odometer_finite`), so
  reading it through `ENat.toNat` in Corollary 1.1(i) and Lemma 4.1 loses nothing. `τ_j` is an
  infimum in `ℕ∞`.
- In Theorem 1.1(i) and Corollary 1.1(i) the dimension is written `d + 1`.
- As in the paper, Sections 2.5–5 work on even cubes `N = 2M`; Theorem 1.1 and Corollary 1.1
  are proved for every `N ≥ 1`.
- Not formalized: the open problems of Section 1 and the figures.

## Guarantees

All 23 theorem-level statements of the corrected edition (its versions of the 20 statement clauses of the published paper, and three added lemmas) are proved in Lean, with no `sorry` and only the standard axioms. Theorem 1.1 and Corollary 1.1 are stated as published, with the quantifier in the definition of `τ_j` made explicit.

[`ledger/manifest.yaml`](ledger/manifest.yaml) records these 23 statements together with six statements
that characterize the definitions they use, 29 in all; the block below is generated from it.

<!-- STATUS-BEGIN (generated by python3 -m leanform_tools.sync_docs) -->

Status: **29 statements in `ledger/manifest.yaml`: 29 proved.**  The 29 proved statements have complete proofs whose axiom closures contain no `sorryAx`.  These
counts are generated from `ledger/manifest.yaml` by
`python3 -m leanform_tools.sync_docs`, which fails when they disagree with it.

<!-- STATUS-END -->

- **No `sorry`** in `DimRed/`, and the build emits no warning. The four comparator challenges
  under [`DimRedAudit/`](DimRedAudit/) carry ten intentional statement-level `sorry`s, one per
  challenge theorem, which the corresponding solutions prove.
- **Standard axioms only.** [`DimRed/Meta/AxiomsAudit.lean`](DimRed/Meta/AxiomsAudit.lean)
  prints the axiom report of every result of `DimRed/MainTheorems.lean` and of the six
  definitional statements, and [`scripts/check_axioms.py`](scripts/check_axioms.py) requires
  exactly `propext`, `Classical.choice` and `Quot.sound` for each theorem of its explicit list.
  [`CERTIFICATE.md`](CERTIFICATE.md) records the axiom closures and the statement hashes.
- **Statement hashes.** The text of every statement in `DimRed/Frozen/` is fixed by its
  SHA-256 in [`ledger/manifest.yaml`](ledger/manifest.yaml), together with the hash of the
  corrected edition; `python3 tools/verify.py` checks them, the paper correspondence and the
  axiom closures.
- **Independent check of the main statements.** Theorem 1.1, Corollary 1.1 and the five
  clauses of Proposition 4.1 are restated in [`DimRedAudit/`](DimRedAudit/) over definitions
  rebuilt from Mathlib alone, in four challenge/solution pairs; the solutions prove the
  restatements from the library, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks them with the Lean
  kernel and the nanoda kernel. The other results (Sections 2 and 3, Lemmas 4.1 and 5.1) have
  no comparator pair.
- **Pinned toolchain and dependencies.** Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` and Lattice-Probability
  `d6dc1aaae0ad1bdfd353cb7e1817a41406131e18`, recorded in
  [`lake-manifest.json`](lake-manifest.json).

## Size

`DimRed/` and `DimRed.lean`: 112 Lean files with 21,312 lines (17,871 lines of code once
comments and blank lines are removed). The comparator surface `DimRedAudit/` is counted
separately: 16 files with 1,601 lines.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                   # prebuilt Mathlib
lake build                           # the library
lake build DimRed.Meta.AxiomsAudit   # print the axioms of every result
lake build DimRedAudit               # the comparator challenges and solutions
```

`python3 tools/verify.py` runs the repository's checks (statement hashes, paper
correspondence, axiom closures, warning census); it needs Python 3.10 or newer and PyYAML
(`python3 -m pip install -r tools/requirements.txt`). [`CONTRIBUTING.md`](CONTRIBUTING.md)
describes each check. To build the corrected edition, run `latexmk -pdf
dimred-corrected-arxiv.tex` in [`paper/corrected-arxiv/`](paper/corrected-arxiv/).

## Running the comparators

Each pair `DimRedAudit/<X>/`, for `<X>` in `DimensionalReduction`, `SelfSimilarity`,
`Sandpile` and `Regularity`, has a configuration `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build
`leanprover/comparator`, `lean4export`, `nanoda` and `landrun` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), and run from the
repository root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator DimRedAudit/<X>/comparator.json
```

which prints `Your solution is okay!`. The [comparator workflow](.github/workflows/comparator.yml)
runs all four pairs on manual dispatch; [`DimRedAudit/README.md`](DimRedAudit/README.md)
describes the pairs.

## Repository layout

```text
DimRed/
  MainTheorems.lean   every result, stated in full
  Frozen/             one statement per file: Main/ (Theorem 1.1, Corollary 1.1), Prelim/
                      (Section 2), BaseCase/ (Section 3), Regularity/ (Proposition 4.1,
                      Lemmas 4.1 and 5.1), Definitions/ (definitional statements)
  Support/            the definitions and the proofs, including the joint induction of
                      Sections 4 and 5
  Meta/               AxiomsAudit.lean
DimRed.lean           the root module
DimRedAudit/          the Mathlib-only comparator challenges, solutions and bridges
paper/corrected-arxiv/  the corrected edition: source, bibliography, figures, source note
paper/dimred-arxiv.tex  the unmodified arXiv source (v2)
ledger/               the statement manifest (manifest.yaml), the clause and exponent
                      readings (readings.yaml) and the list of open proofs used by the progress
                      check (holes.json, empty)
CORRESPONDENCE.md     paper ↔ Lean: vocabulary, standing hypotheses, statement table
ASSUMPTIONS.md        the cited results assumed (none; generated)
CERTIFICATE.md        the axiom closures and statement hashes (generated)
scripts/              the explicit-list axiom check
tools/                verify.py and the vendored checker package tools/leanform/
.github/workflows/    build and comparator workflows
```

## How this was built

The Lean code was written by AI coding agents (Anthropic Claude models through Claude Code,
OpenAI GPT models through the Codex CLI, and DeepSeek models for auxiliary proof search) under
the close supervision of the author. The changes of the corrected edition, its corrections
section and its new proofs were also drafted by these agents and checked by the author; the
corrected edition ends with a statement on the use of artificial intelligence. Every proof is checked by the Lean kernel. The models and
tools are listed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development and paper are by **Ahmed Bou-Rabee**. To cite the development, use
[`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see
[`LICENSE`](LICENSE)).  The paper source in `paper/` is included for reference and is not
covered by the Apache license.

## Palomar preflight

The manually dispatched [Palomar full preflight](.github/workflows/palomar-preflight.yml)
calls Palomar's complete verifier at a pinned revision. Select the repository-relative
Comparator configuration to check. It records the dispatched commit and runs with
`mode: full` and `execution_profile: palomar-standard-v1`. Resolve the current Lean
minimum, source-module, Challenge-closure, licensing and metadata requirements before
dispatch. A passing preflight is advisory; it is separate from submission, editorial
review and a public registry record.

The module compatibility revision preserves the mathematical definitions and frozen
statements. Its pinned Lattice-Probability source adds public module interfaces and
updates two existing walk-proof calls to the current Mathlib API. Full Palomar
verification checks the selected Challenge/Solution pair at the dispatched commit.
