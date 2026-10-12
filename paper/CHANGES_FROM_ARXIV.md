# Differences from the arXiv version

The current Lean manifest pins `paper/dimred.tex`, a locally corrected copy of
arXiv:2009.05968v2 with the ten changes documented below. The author selected
the unmodified arXiv v2 paper as the final formalization target. These local
changes are historical proposals, not an adopted replacement of that source;
their source and proof consequences remain under review. The arXiv source is
`paper/dimred-arxiv.tex`.  The first eight changes and the three added labels
keep the line count, so a line number up to 1325 is the same line in both
files.  The tenth change edits line 1325 in place and inserts one line after
it, and replaces line 1329 by two lines, so arXiv lines 1326 to 1328 are lines
1327 to 1329 of the corrected file and arXiv lines 1330 to 1333 are lines 1332
to 1335.  From arXiv line 1334 (corrected line 1336) onward the ninth change
replaces and extends the passage, and later line numbers differ.  Line 1321
differs only by a trailing space, which the corrected file drops; this
whitespace change is not one of the ten.  The figures and `main.bbl` of the
arXiv source are not included in this repository.

## 1. The topple time in Theorem 1.1

Section 1.2, Theorem 1.1 (`the_theorem`), the definition of `τ_j`, line 128.

arXiv:

    \tau_j := \min\{ t \geq 1 : v_t^{(d,2j)}(x) \geq j for x \in \partial C_{2j}^{(d)} \}

Corrected:

    \tau_j := \min\{ t \geq 1 : v_t^{(d,2j)}(x) \geq j for some x \in \partial C_{2j}^{(d)} \}

Read over every inner boundary site, the set is empty once `d ≥ 2` and `j ≥ 3`:
the terminal odometer of `s_0 ≡ 2d` on `C_{2j}^{(d)}` is only `2` at the corners
of the boundary.  Then `τ_j` is infinite, the hypothesis `t ≤ τ_j` constrains
nothing, and self-similarity in Theorem 1.1, the self-similarity clause of
Proposition 4.1 and both strong facet clauses become false.  With "for some",
`τ_j` is the first time `v_t(j, 1_{d-1}) ≥ j`, because the maximum of `v_t`
over the inner boundary is attained at that corner, and it lies inside the
window of times on which self-similarity holds.

## 2. Nonnegative initial sandpile in Section 2.2

Section 2.2 (Babai-Gorodezky technique), the standing hypothesis before Lemma 2.1
(`pt_ind_lemma`), line 288.

arXiv: "let `s_0 ≤ 2(2d) - 1` be an arbitrary initial sandpile on `C`"

Corrected: "let `0 ≤ s_0 ≤ 2(2d) - 1` be an arbitrary initial sandpile on `C`"

Lemma 2.1 is false for a negative initial sandpile: for `s_0 ≡ -1` every `v_t`
vanishes, while the right-hand side of the lemma is `⌊-1/2d⌋ = -1`.  A sandpile
is a number of chips at each site, so the lower bound makes explicit what the
word means elsewhere in the paper.

## 3. The first boundary branch of Lemma 2.4

Section 2.5, Lemma 2.4 (`general_difference_comparison`), display
`eq:boundaries_ref`, line 481.

arXiv:

    \sup_j ( \sum_{y \sim x} v_t(y) - \sum_{y' \sim (x+w_j)} v_t(y') - 2d g_j(x) ) \leq 0

Corrected:

    \sup_j ( \sum_{y \sim x} v_t(y) - \sum_{y' \sim (x+w_j)} v_t(y') - 2d g_j(x) ) \leq 0
        and x + w_j \in C_N for all j

The first branch bounds a difference of neighbour sums, and the proof turns it
into a bound on `v_{t+1}(x) - v_{t+1}(x + w_j)` by applying Lemma 2.1 at
`x + w_j`.  That step needs `x + w_j` in the cube: off the cube `v_{t+1}` is the
padded value `0` while the neighbour sum is not.  Every use of the lemma in the
paper satisfies the condition, and on the dissipating boundary the paper uses
the second branch.

## 4. Axis monotonicity, Corollary 2.1

Section 2.5, Corollary 2.1 (`axis_monotonicity`), lines 514 to 522 and line 526.

arXiv: "For all `t ≥ 1`, `x ∈ S`, and all sets of indices
`I = {i_1, ..., i_n : 1 ≤ i_1 < ... < i_n ≤ d}` and
`J = {j_1, ..., j_m : i_n < j_1 < ... < j_m ≤ d}` where `n ≥ 1` and `m ≥ 0` we
have `v_t(x) ≥ v_t(x + e_I - e_J)` for `(x + e_I - e_J) ∈ S`", with `e_I` the sum
of the basis vectors indexed by `I`.

Corrected: "For all `t ≥ 1`, `x ∈ S`, every index `1 ≤ i ≤ d`, and every set of
indices `J` that is either empty or equal to `{j}` for an index `i < j ≤ d`, we
have `v_t(x) ≥ v_t(x + e_I - e_J)` for `(x + e_I - e_J) ∈ S`, where `I = {i}`".
The bound variable of the sum defining `e_I` is renamed from `i` to `k`.

The statement for general index sets is false.  Take `d = 3`, `M = 4` and the
constant initial sandpile `s_0 ≡ 8`, `I = {1}` and `J = {2, 3}`.  Both
`x = (2,2,2)` and `x + e_I - e_J = (3,1,1)` lie in `S_4^{(3)}`, and
`v_8(3,1,1) = 8 > 7 = v_8(2,2,2)`.  The corrected statement is that of Babai and
Gorodezky, whom the corollary cites: a function is axis monotone when it does
not increase along one step perpendicular to one axis of symmetry, away from
that axis.  On `S_M^{(d)}` these steps are `e_i`, perpendicular to a reflection
axis, and `e_i - e_j` with `i < j`, perpendicular to a rotation axis.  The use of the
corollary in Section 5 is a chain of such steps.

## 5. The ripple clause of Proposition 3.2

Section 3.2, Proposition 3.2 (`prop:base_case`), display `eq:ripple`, lines 798
and 800.

arXiv: "for each `t' < t` and `a_{t'-1} ≥ x > a_{t'}`,
`v_t(x) = v_{t-1}(x - 1)`"

Corrected: "for each `t' < t ≤ t' + x` and `a_{t'-1} ≥ x > a_{t'}`,
`v_t(x) = v_{t'}(x - (t - t'))`"

The arXiv clause fails in two ways.  At the radial origin it asserts
`v_t(0) = v_{t-1}(-1) = 0`, which is false for `t ≥ 1`.  Away from the origin it
fails as soon as the next ripple front has reached `x - 1` but not yet `x`: for
`d = 2`, `t' = 2`, `x = 2` and `t = 6` it asserts `v_6(2) = v_5(1)`, while the
odometer of `s_0 ≡ 5` on `C_4^{(2)}` has `v_6(2) = 2` and `v_5(1) = 3`.  What
Step 2 of the proof establishes is that the front advances one site per step,
so that outside the firing block the profile at time `t` is the profile at time
`t'` shifted outward by `t - t'`, as long as the shift stays inside the
domain.  That is the corrected clause.

## 6. Weak facet compatibility in Proposition 4.1

Section 4, Proposition 4.1 (`base_dimension`), display
`base_dimension:weak_compatability`, line 924.

arXiv conclusion: `v_{t+1}(x_i, 1, 1_j) = v_{t+1}(x_i, 1, 1_j)`

Corrected conclusion: `v_{t+1}(x_i, 1, 1_j) = v_t(x_i, 1, 1_j)`

The arXiv conclusion is a tautology.  The corrected one says that the site does
not topple at this step, which is what the proofs for `d = 1` and `d ≥ 2`
derive and what Section 5 uses.

## 7. Strong facet compatibility in Proposition 4.1

Section 4, Proposition 4.1 (`base_dimension`), display
`base_dimension:strong_compatability`, line 935.

arXiv hypothesis: `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1) + 1`

Corrected hypothesis: `v_t(x_i, 1, 1_j) = v_t(x_i, 2, 1_j) + 1`

The subscript `j` was missing; the point is `(x_i, 2, 1_j)` everywhere else in
the display and in the proof.

## 8. Step 2 of the proof of Proposition 3.2

Section 3.2, the proof of Proposition 3.2 (`prop:base_case`), Step 2, lines 853
to 887.

arXiv: Step 2 takes `x` in the window `a_{t'} < x ≤ a_{t'-1}` and checks two
configurations of `v_t(x-1), v_t(x), v_t(x+1)`: a jump of one at `x`, where it
shows that `x` topples and `x - 1` does not, and three equal values `t' - 1`,
where it shows that `x` does not topple.

Corrected: Step 2 proves the corrected clause of change 5 at time `t + 1` from
both clauses at time `t`.  It reads `v_t` near `x` off the clause for the window
of `x` and, at the two ends of the window, off the clauses for the neighbouring
windows, and splits into three cases: `x` behind the ripple front, just ahead
of it, and further ahead.  In each case the radial Laplacian gives the sign of
`s_t(x) - 2d`, so it decides whether `x` topples, as the clause requires.

The arXiv argument proves the one-step clause that change 5 replaces, and
leaves out the case of `x` behind the front and the values at the two ends of
the window.  The corrected Step 2 follows the proof of `ripple_shift` in
`DimRed/Support/BaseInduction.lean`.

## 9. Case 2 of the strong derivative clause in Section 5

Section 5.2, the proof of the strong derivative clause
`base_dimension:strong_derivative` of Proposition 4.1 for `d ≥ 2`, Case 2,
lines 1334 to 1428 (arXiv lines 1334 to 1362), and the range of `i` in Case 1,
line 1325.

arXiv: Case 2 (`t ≥ τ_M`, `i ≥ 2`) claims

    v_t(x) - v_t(x + 2 e_i) \leq 2 x_i    for all sorted x with x_1 \geq 2 and i \geq 2,

by Lemma 2.4 with a dissipating boundary `x_j = M - 1`, on which it claims
`v_t(x) ≤ v_t(M, 1_{d-1}) ≤ M` by axis monotonicity, and a reflecting boundary
checked as for `d = 1` apart from the point `(2, 1_{d-1})`.  Case 1 states its
family for "all `d ≤ i ≤ 1`".

Corrected: Case 2 proves `eq:two_derivative_bound`, `v_t(x_{i-1}, 1, 1_j) -
v_t(x_{i-1}, 3, 1_j) ≤ 2` for `x_{i-1} ≥ 2` and `i ≥ 2`, at every time `t`.  Case 1
states its family for all `1 ≤ i ≤ d`.

Both intermediate claims of the arXiv Case 2 are false.  For `d = 2`, `M = 4` and
`t = 16 ≥ τ_4 = 13` the odometer of `s_0 ≡ 4` has `v_{16}(2,2) - v_{16}(4,2) = 9 - 4
= 5 > 4`, a point with `x_1 = x_2` where the family fails.  For `d = 2`, `M = 3`
and `t = τ_3 = 7`, the point `(2,2)` has `x_2 = M - 1` and `v_7(2,2) = 4 > 3 =
v_7(3,1)`.  The family is not closed under permutations of the coordinates, so
the rotating boundary of Lemma 2.4 would have to be checked, and it is exactly
there that the family fails.  The strong derivative clause itself is true.

The corrected Case 2 works on the positive orthant `P_M = {1, ..., M}^d`, where
by symmetry a neighbour of a point either lies in `P_M`, is a reflection of the
point itself, or lies off the cube.  With Lemma 2.1 it proves, by induction on
the time `s ≤ t`, five bounds for `x ∈ P_M`:

1. `v_s(x) - v_s(x + e_k) ≤ x_k`, from Corollary 2.2, whose hypothesis follows
   from the parabolic least action principle applied to the one-dimensional
   odometer in the coordinate `x_l`;
2. `v_s(x) - v_{s-1}(x + e_k) ≤ x_k`;
3. `v_s(x + e_k) ≥ v_{s-1}(x)` when `x_k = 1` and some coordinate is at least `2`;
4. `v_s(x) - v_s(x + e_k + e_l) ≤ x_k + x_l - 1` for `k ≠ l`;
5. `v_s(x) - v_s(x + 2 e_k) ≤ 2 x_k` when `x_k` is smaller than the largest
   coordinate of `x`.

Weak facet compatibility enters at the reflecting boundary in 2 and 5, and
strong facet compatibility with a nonempty head gives 3; both are used only at
times before `t`, where they hold by induction.  Bound 5 at the point
`(x_{i-1}, 1, 1_j)`, whose `i`-th coordinate is `1 < x_1`, is the clause.  The
restriction in 5 to coordinates below the maximum is necessary: for the largest
coordinate the bound fails by one after `τ_M`, which is why the clause at
`t ≥ τ_M` requires `i ≥ 2`.  The argument does not use `t ≥ τ_M`, so Case 1 is
needed only for the point `1_d`.

## 10. The missing boundary checks of Case 1 in Section 5.2

Section 5.2, the proof of the strong derivative clause
`base_dimension:strong_derivative` of Proposition 4.1 for `d ≥ 2`, Case 1,
lines 1319 to 1333.

arXiv: Case 1 applies Lemma 2.4 (`general_difference_comparison`) with the
points `2e_1, ..., 2e_d` to prove `v_t(x) - v_t(x + 2e_i) ≤ 2x_i` for all
`1 ≤ i ≤ d`.  It checks the dissipating boundary, asserting
`v_t(x) - v_t(x + 2e_j) ≤ 2(M-1)` on `∂_{2e_j} S_M`, and says the reflecting
boundary is checked as for `d = 1`.  It does not say why the rotating
boundary needs no separate check, and it does not say why `v_t(x) ≤ M - 1`
there.

Corrected: two sentences are added.  Since the displayed bound holds for
every index `i`, permuting the coordinates carries it from one index to
another, by Lemma 2.3 (`symmetry_lemma`); this is why the rotating boundary
needs no separate check.  On the dissipating boundary, `t < τ_M` gives
`v_t(x) ≤ M - 1` whenever a coordinate of `x` equals `M`; combined with the
one-step bound at `x_j = M - 1`, this derives the stated bound `2(M-1)`
instead of asserting it.

Both facts are true.  Lemma 2.4 controls the points `w_1, ..., w_n` together,
with one boundary check per point at each `x`; Case 1 takes `w_j = 2e_j` for
every `1 ≤ j ≤ d`, the same displayed bound at every index.  A point of the
rotating boundary for `w_j` becomes, after the permutation that resorts
`x + w_j`, a point of `S_M` where the bound for some other `w_{j'}` already
applies, so no separate rotating boundary argument is needed.  By the
definition of `τ_M`, no point of the inner boundary of the cube reaches `M`
before time `τ_M`, which gives `v_t(x) ≤ M - 1` there; at `x_j = M - 1`, the
one-step bound `v_t(x) - v_t(x + e_j) ≤ x_j` and this boundary value together
give `v_t(x) - v_t(x + 2e_j) ≤ (M-1) + (M-1)`.

## The strong-facet comparison in Section 5

`dimred.tex:1288-1296` (the paragraph between the displays
`eq:laplace_21`-`eq:laplace_23` and `eq:laplace_12`).

As written, the paragraph closes the comparison `eq:laplace_11 ≥ eq:laplace_21`
by observing that `v_t(x_i - e_{j'}, 2, 1_j) = v_t(x_i, 1, 1_j) ≥ v_{t-1}(x_i, 1, 1_j)`
when `x_i - e_{j'} ≱ 2`.  The term on the right of `eq:laplace_21` is
`v_{t-1}(x_i - e_{j'}, 1, 1_j)`, not `v_{t-1}(x_i, 1, 1_j)`, so the comparison
needs `v_{t-1}(x_i, 1, 1_j) ≥ v_{t-1}(x_i - e_{j'}, 1, 1_j)`, which is the
opposite of axis monotonicity (Corollary 2.1) and is false.  Measured on the
dynamics of Section 1 for `j ≤ 2`, `M ≤ 6` and every `t`: 145 failures of that
inequality, and 40 failures of `eq:laplace_11 ≥ eq:laplace_21` itself; the
smallest is `j = 0`, `M = 2`, `t = 3`, where `v_{t-1}(2,1) = 1 < 2 = v_{t-1}(1,1)`.

Corrected: the development does not use the comparison.  The gap one step back
in time, which is what the unit-gap branch of Section 5 needs, follows from the
gap at the current time together with the first-difference bound of Corollary
2.2; that step is `DimRed.odo_jump_of_gap` in `DimRed/Support/RegBridges.lean`.
The strong-facet clause itself follows from strong facet compatibility one step
back together with the first-difference bound, and is formalized as
`DimRed.facet_step_of_earlier` in `DimRed/Support/FacetStepFinal.lean`; the
first-difference bound at a coordinate equal to one supplies only the "stays
put" half of the clause (`DimRed.strong_facet_step_of_reg`).  The joint
induction of Section 5 is carried out with `odo_jump_of_gap` and
`facet_step_of_earlier`.  The ruling, this corrected attribution and the
evidence are recorded in `ledger/decisions.md`.

## Labels on three statements

The corollary at `dimred.tex:143` (Corollary 1.1), the proposition at
`dimred.tex:706` (Proposition 3.1) and the lemma at `dimred.tex:728`
(Lemma 3.1) carried no `\label`, so no node could claim them by name.  They now
carry `\label{sandpile_corollary}`, `\label{no_reduction}` and
`\label{radial_laplacian}`, each on the line of its `\begin`, so no line number
moves and no mathematical text changes.
