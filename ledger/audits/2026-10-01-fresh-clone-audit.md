# Independent refute-first audit from a fresh clone

Date: 2026-10-01.  Auditor: independent, refute-first, read-only with respect to everything
audited; this file is the only change it makes to the repository.  Commit audited:
`b0c8914` (the `main` HEAD at the start, clean tree).  While the audit ran, `main` advanced to
`e9ff283` (five commits: two comment lines on heartbeat budgets, one lemma rename, ledger and
documentation records), and again while this report was being written; the hash, build and
axiom checks were repeated at `e9ff283` and are reported where they differ.

Claim under test: at the pinned commit the repository faithfully transcribes
`paper/dimred.tex`; every sealed node is proved with axiom closure exactly
`{propext, Classical.choice, Quot.sound}`; no binder is EXCESS; the consumers are sound; the
record is consistent.

**Result: not refuted.  No FAIL.  Four CONCERNs, none affecting a statement, a proof or an
axiom closure.  The strongest refutation attempt (§4) fails.**

## 1. Verdict table

| # | check | verdict | machine evidence |
|---|---|---|---|
| 1 | paper pin: `sha256(paper/dimred.tex)` = `source_pin.sha256` | PASS | `1423810f…12b3ef`, recomputed with `sha256sum`, at `b0c8914` and `e9ff283` |
| 2 | `frozen_sha256` of all 20 nodes, recomputed by my own script (bytes strictly between the markers, one leading newline dropped) | PASS | 20/20 equal to `ledger/manifest.yaml` and to the table in `CERTIFICATE.md`, at both commits |
| 3 | manifest ↔ frozen tree: files one-to-one, declared name = `export`, exactly one marker pair per file, text after the end marker begins the proof | PASS | 20/20 |
| 4 | record: every node carries `approved:` | CONCERN | `lem-difference-comparison` has none; the field has been absent since `c0f7529` (2026-09-13), when version 3 of the node was registered; all 19 other nodes carry one |
| 5 | `paper/dimred.tex` vs `paper/dimred-arxiv.tex` against `paper/CHANGES_FROM_ARXIV.md` | PASS (note) | `diff` has 226 changed lines; every hunk is one of the ten listed changes or one of the three added labels.  Note: the change list says a line number before 1334 is the same in both files; change 10 inserts one line at 1326, so arXiv 1326–1333 are corrected 1327–1334.  No manifest `source:` range lies above 950.  A whitespace-only change at line 1321 is not listed |
| 6 | clean `lake build DimRed` from a fresh `git clone` | PASS | exit 0, 8759 jobs, 0 warnings, 0 errors, 0 `sorry`; wall 3 m 32 s; Mathlib oleans from `lake exe cache get`, `LatticeProb.Site` and all 101 `DimRed` modules compiled from source; repeated incrementally at `e9ff283`: exit 0, 8759 jobs |
| 7 | `#print axioms` on every export, every restatement, the induction root, the three discharged steps and the finiteness lemmas | PASS | 49/49 closures are exactly `[propext, Classical.choice, Quot.sound]`; `example : ConsistStepHyp := consist_step_of_earlier` (and the facet, topple analogues) elaborate, so `reg_proved` has no hypothesis |
| 8 | banned constructs in the production tree and in the dependency actually imported | PASS | no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern` under `DimRed/`; the only `LatticeProb` import is `LatticeProb.Site` (`Site`, `unit`) |
| 9 | elaborated-binder five-bin audit, all 20 nodes (§3) | PASS | EXCESS 0; the one implicit binder in the frozen surface is `{n : ℕ}` of Lemma 2.4 (TYPING); `autoImplicit` is off, no auto-bound or instance binder appears in any `#check @` |
| 10 | consumers: `DimRed/MainTheorems.lean` | PASS | a meta command compared `ConstantInfo.type` of each `DimRed.Frozen.X` with `DimRed.X`: `Expr` equality true for 20/20; every proof is `exact` of the frozen export |
| 11 | consumers: comparator surface `Audit/` | PASS | vocabulary block byte-identical in the three challenges and `Support/Vocabulary.lean` (sha `5655819e…`); each challenge elaborates against Mathlib alone with exactly one `declaration uses sorry` per theorem (2 + 1 + 2); `lake build Audit` exit 0 (8751 jobs); the 5 solution theorems and the bridges `odo_eq`, `toppleTime_eq`, `sandpInfUnif_eq` have the three-axiom closure; challenge, solution and `MainTheorems` statement texts are identical token for token |
| 12 | gates: `python3 tools/verify.py` with the Lake gates, on the fresh tree | PASS | 15/15 OK, each gate inspecting at least one item; `check_warnings` saw a no-warning build; `check_axioms` reported all 20 clean; `certificate --check` OK |
| 13 | non-vacuity: the `ℕ∞` junk values and the hypotheses that could be trivialised or made unsatisfiable by them (§5) | PASS | proved from the development with clean closure: `toppleTime d j ≠ ⊤` for `d, j ≥ 1`; `odoInfUnif d N x ≠ ⊤` for `d ≥ 1`; `odoInfUnif d (2j) (j, 1_{d-1}) = j`; executable witnesses at small parameters agree with the statements and with the paper's `τ_j = j(j-1)+1` |
| 14 | record consistency: `CERTIFICATE.md`, `CORRESPONDENCE.md`, `README.md`, `formalization.yaml`, `FRONTIER.md`, `decisions.md`, `readings.yaml` | CONCERN | mutually consistent on every count and hash I compared; the two readings awaiting the owner (strong-derivative `x`, strong-facet erratum narrative) are still open at `e9ff283`; they are the owner's and are not approved here |
| 15 | hypotheses the frozen surface carries beyond the paper's letter | CONCERN | `lem-symmetry` and `lem-topple-limit` demand `IsSymmetricPile d N s₀` on all of `ℤ^d`, while the paper's `s_0` lives on `C`; every paper instance is covered through the zero extension, so this is not a weakening (§4) |
| 16 | hygiene (no verdict impact) | note | `abel` at `DimRed/Support/Difference.lean:18` emits the info `Try this: abel_nf` on every build (info, not warning); `FoldGtOne.lean` and `TwoPointTopple.lean` are compiled by the default target but imported by nothing; ten `Support` modules import sealed `Frozen.Prelim` modules |

## 2. Procedure

1. Pinning.  Recomputed the paper hash and every frozen hash with an independent script,
   compared the declared theorem names with `export:`, the frozen directory with the
   manifest, and the `CERTIFICATE.md` table with the manifest.  Checked every `source:` line
   range against the `\begin{…}`/`\end{…}` lines and labels of the tex.
2. Paper.  Diffed `paper/dimred.tex` against `paper/dimred-arxiv.tex` and matched every hunk
   to `paper/CHANGES_FROM_ARXIV.md`.
3. Fresh build.  `git clone` of the repository into a scratch directory, `lake exe cache get`,
   `/usr/bin/time -v lake build DimRed`; grep of the log for `warning`, `error`, `sorry`.
   Then `lake build Audit`, `bash Audit/check_standalone.sh` on the three challenges and on
   `--vocabulary`, and `python3 tools/verify.py --keep-going` with the Lake gates.
4. Axioms and consumers.  A probe file importing `DimRed` printed the axiom closure of the
   20 exports, the 20 restatements, `reg_proved`, `reg_all`, the three step theorems,
   `odoInf_finite`, `toppleTime_ne_top`, `toppleTime_eq_corner` and `corner_reaches`;
   a meta command compared the elaborated types of each frozen export and its restatement;
   `#check @` printed the elaborated binders of the 20 exports; `#print` printed the bodies of
   the definitions the statements are read through.  A second probe importing the three
   solutions printed their closures.
5. Statement audit.  Each frozen statement was reconstructed from the pinned tex and every
   elaborated binder was placed in one of five bins (§3).
6. Non-vacuity.  Three theorems proved in the probe and `#eval` of the compiled definitions
   at small parameters (§5).
7. Everything was repeated at `e9ff283` where the audited surface could have moved: hashes,
   build, axiom closures and type identity.

## 3. Elaborated-binder five-bin audit

Bins: SOURCE (written in the statement), STANDING (a standing assumption of the section the
statement lives in, cited), TYPING (a declaration of what kind of object a variable is),
RULED (fixed by an owner ruling), EXCESS (none of these).  Binders are those of `#check @`.

| node | SOURCE | STANDING | TYPING | RULED | EXCESS | notes |
|---|---|---|---|---|---|---|
| `lem-pt-ind` | `t`, `x`, `inCube d N x` (289–290) | `1 ≤ d`; `hs0`, `hs1` on the cube (288, as corrected §2) | `d N s₀` | — | 0 | integer division is floor division for `2d > 0` |
| `lem-parabolic-comparison` | the constraint, `u ≥ 0`, `u = 0` off `C` (312: `u : G → ℤ⁺`, `G = ℤ⁺ × C`) | as above | `d N s₀`, `u` | — | 0 | a minimum of functions stated as its two halves |
| `lem-symmetry` | `t` (416, `t ≥ 0`), `π ε` (σ ∈ Aut), `IsSymmetricPile` (369) | — | `d N s₀ x` | — | 0 | stronger than the paper: the bound `0 ≤ s_0 ≤ 4d−1` is not carried; `x` ranges over `ℤ^d`; see §4 on the domain of `IsSymmetricPile` |
| `lem-difference-comparison` | `w g` (474), `hg` (474), `t₀`, `hinit` (476), `hbdry` (478–485 as corrected §3) | `1 ≤ d`; `c`, `hc0`, `hc1` (440 constant pile; 288 bound, which the proof needs through Lemma 2.1) | `d M`, `{n}` | — | 0 | `bdry`'s three pieces are 454, 458, 462 verbatim |
| `cor-axis-monotonicity` | `1 ≤ t` (514), `x ∈ S` (515), `i` (516–517), `J`, `#J ≤ 1`, `i < j` (518–521 as corrected §4), `hmem` (524) | `1 ≤ d`; `c`, `hc0`, `hc1` | `d M` | — | 0 | `_ht` unused by the proof, as the paper's `t ≥ 1` is unused |
| `cor-derivative-bound` | `k`, `1 ≤ k`, `hcorner` (532), `j : Fin d` (533), `t` (533) | `1 ≤ d`; `c`, `hc0`, `hc1`; `x ∈ S` (441) | `d M` | — | 0 | `hcorner` is an inequality in `ℕ∞`; §5 shows `k = 1` satisfies it for the paper's pile |
| `lem-topple-limit` | `t₀ t j`, `t₀ ≤ t` (670) | `1 ≤ d`; `hs0`, `hs1` (288); `IsSymmetricPile d (2M) s₀` (369; version 2) | `d M s₀` | — | 0 | stronger than the paper: symmetric and bounded, not constant |
| `prop-no-reduction` | `2 ≤ d₀` (705) | — | `d₀` | — | 0 | both piles written as the paper writes them |
| `lem-radial-laplacian` | `t`, `k ≤ d` (725, `0 ≤ x ≤ d`) | — | `d`, `c` | — | 0 | stronger than the paper: any constant pile, `d = 0` allowed; the `v_t(−1) = v_t(d+1) = 0` convention is unnecessary because both coefficients vanish |
| `prop-base-case` | `1 ≤ d` (790), `t` (791, as `t+1`), `x ≤ d` (725), `s`, `s+1 ≤ t`, `t−s ≤ x`, `x ≤ a_s`, `a_{s+1} < x` (798 as corrected §5) | — | — | — | 0 | `blockEdge` is `a_t` of 781–790 with `a_0 := d` (853); `ceilSqrt` is `⌈√·⌉` |
| `prop-base-dimension-consistency` | `1 ≤ d`, `2 ≤ M` (913), `1 ≤ j ≤ M`, `t ≤ τ_j` (915), `x > M−j` (917) | `x ∈ S_M` (436) | `d M j t x` | — | 0 | includes `j = M`, as the paper does |
| `prop-base-dimension-weak` | `2 ≤ M` (913), `1 ≤ t`, `x_i ≥ 2` (919), premise `h` (922, conclusion as corrected §6) | `(x_i,1,1_j) ∈ S_M` (436) | `M i j`, `x` | — | 0 | `d = i+1+j` by construction |
| `prop-base-dimension-strong-derivative` | `2 ≤ M` (913), `x_i ≥ 2`, `j ≥ 0` (927), regime `hreg` (928 verbatim) | `(x_i,1,1_j) ∈ S_M` (436) | `M i j t x` | pending | 0 | the paper's bold `x` is read as `(x_i,1,1_j)`, the only true reading (the reading over all of `S_M` is false at `d=1, M=4, t=9`); the owner's confirmation is open in `ledger/decisions.md` |
| `prop-base-dimension-strong-facet` | as above plus premise `h` (935 as corrected §7) | as above | as above | pending | 0 | two conjuncts are the two lines of the display in order |
| `prop-base-dimension-strong-topple` | `1 ≤ d`, `2 ≤ M` (913), `τ_{M−1} ≤ t` (945) | — | `d M t` | — | 0 | `M − 1 ≥ 1` under `2 ≤ M`; `τ_{M−1} < ⊤` (§5) |
| `thm-dimensional-reduction` | `1 ≤ N`, `1 ≤ d` (110, `d ≥ 2` written `d+1`), `1 ≤ t`, `x ∈ S_M^{(d−1)}` (114) | — | `N d t x` | — | 0 | every `N ≥ 1`, odd included |
| `thm-terminal-reduction` | `1 ≤ N`, `1 ≤ d` (110), `x ≥ 2` (118) | `x ∈ S_M^{(d−1)}` (inherited from 114) | `N d x` | — | 0 | an equality of finite values in `ℕ∞` (§5) |
| `thm-self-similarity` | `1 ≤ N`, `2 ≤ d` (110), `j < M`, `t ≤ τ_j`, `x ∈ S_M`, `x > M−j` (122) | — | `N d j t x` | — | 0 | `τ_j` as corrected §1 |
| `cor-sandpile-reduction` | `1 ≤ N`, `1 ≤ d`, `x ∈ S_M^{(d−1)}`, `x ≥ 2` (149) | — | `N d x` | — | 0 | `s_∞ = 2d + Δ v_∞`, `v_∞` finite (§5) |
| `cor-sandpile-self-similarity` | as `thm-self-similarity` with `x > M−j+1` (153) | — | as above | — | 0 | |

Totals over the 20 nodes: EXCESS 0, RULED 0 (two readings pending the owner, both recorded).
Every definition the statements are read through was printed and compared with the paper:
`inCube` is `[1−⌊N/2⌋, ⌈N/2⌉]^d` (277, both parities); `inSimplex` is `M ≥ x_1 ≥ ⋯ ≥ x_d ≥ 1`
(110); `odo` is the paper's recursion with `s_t = s_0 + Δ v_t` (100–107), zero off the cube
(the padding of 280); `toppleTime` is the corrected `τ_j` of 128 as an `sInf` in `ℕ∞`;
`cubeSym` is a signed permutation followed by the translation that preserves the cube
(348–349), `lo + hi = 1` for even `N` and `2` for odd; `facetPoint x c j = (x_i, c, 1_j)`;
`cornerPoint = (M, 1_{d−1})`; `radial d k = (2_k, 1_{d−k})`; `blockEdge` is `a_t`.

## 4. The strongest refutation attempt, and why it fails

The best candidate for "a frozen statement weaker than the paper's" is the symmetry
hypothesis.  Lemma 2.3 and Lemma 2.5 assume (369) an initial sandpile on `C_N` that is
invariant under `Aut_{C_d}`.  The frozen `lem-symmetry` and `lem-topple-limit` assume
`IsSymmetricPile d N s₀`, invariance of `s₀ : ℤ^d → ℤ` under `cubeSym` at every point of
`ℤ^d`, not only on the cube.  A pile that is symmetric on the cube and arbitrary off it does
not satisfy the hypothesis as written.  The attempt fails because `odo` reads `s₀` only on
the cube (`odo_eq_zero_outside`, and the recursion tests `inCube` before reading `s₀`), and
`cubeSym` maps the cube to itself and its complement to itself, so the zero extension of any
paper instance satisfies `IsSymmetricPile` and has the same odometer.  Every instance of the
paper's lemmas is therefore an instance of the frozen statements after a change of
representative that does not change `v_t`.  This is recorded in `ledger/readings.yaml`
(`lem-symmetry`) and is consistent with `CORRESPONDENCE.md`; it is a CONCERN only because
the version-3 repair of `hs0`/`hs1` restricted the bounds to the cube for exactly this reason
while the symmetry hypothesis was left global.

Other attempts, all failed:

- The strong-derivative clause read over all `x ∈ S_M` is false (`d = 1, M = 4, t = 9 < τ_4`,
  `v_9(2) − v_9(4) = 3`), so the frozen reading `x = (x_i,1,1_j)` is not a weakening of a
  true statement but the only true statement the display can mean; the paper's own use of it
  (1263–1265, 1029) is that reading.
- `τ_j = ⊤` would make `t ≤ τ_j` trivially true and `τ_M ≤ t`, `τ_{M−1} ≤ t` unsatisfiable;
  `v_∞ = ⊤` would make the terminal equalities `⊤ = ⊤` and `s_∞` read `toNat ⊤ = 0`.  Both are
  excluded by theorems with clean closure (§5).
- The three induction-step hypotheses of `reg_all` could have been smuggled as assumptions;
  they are discharged by theorems whose types are exactly `ConsistStepHyp`, `FacetStepHyp`,
  `ToppleStepHyp`, and `reg_proved` has no hypothesis.
- The ten statements of Theorem 1.1, Corollary 1.1 and Proposition 4.1 could have been read off
  the induction with weaker hypotheses; the bridges `*_of_reg` are stated with the frozen
  binders verbatim and the frozen proofs apply them to `reg_proved` with no other argument.
- A restatement in `MainTheorems.lean` could differ from the frozen export it claims to
  restate; the elaborated types are `Expr`-equal for all 20.

No frozen statement is weaker than its paper statement.  Five are stronger in a way the record
documents: `lem-symmetry` drops the bound on `s_0`; `lem-radial-laplacian` holds for every
constant pile and at `d = 0`; `lem-topple-limit` needs symmetry, not constancy; `lem-pt-ind`
and `lem-parabolic-comparison` need the bounds only on the cube; the main theorems hold for
every `N ≥ 1`, including the odd cubes and `M = 1` that the paper treats in passing.

## 5. Non-vacuity

Proved in the probe (`#print axioms`: `[propext, Classical.choice, Quot.sound]` for each):

```
theorem aud_toppleTime_ne_top (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j) : toppleTime d j ≠ ⊤
theorem aud_odoInfUnif_ne_top (d N : ℕ) (hd : 1 ≤ d) (x : Site d) : odoInfUnif d N x ≠ ⊤
theorem aud_corner_terminal (d j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j) :
    odoInfUnif d (2 * j) (cornerPoint d j) = (j : ℕ∞)
```

The first is `toppleTime_ne_top` fed by `corner_reaches`, whose dimensional-reduction
hypothesis is `dimensional_reduction_all_of_reg reg_proved` at `N = 2j`; the second is
`odoInf_finite` (stabilisation of every bounded pile) through `odoInf_eq_of_stable`; the
third is `odoInfUnif_corner_eq` fed the same way.  The third also shows that the corner
hypothesis of Corollary 2.2 is satisfied with `k = 1` by the paper's pile, so
`cor-derivative-bound` has a non-vacuous instance in every dimension and size.

Executable witnesses (`#eval` of the compiled definitions, not of the development's lemmas):

| statement | parameters | evaluated | reads |
|---|---|---|---|
| `τ_j`, through `toppleTime_eq_corner` | `d = 1, 2`; `j = 1, 2, 3` | `1, 3, 7` in both dimensions | `j(j−1)+1`, independent of `d`, finite |
| Theorem 1.1(i), first display | `N = 5` (odd), paper `d = 2`, `x = (2)`, `t = 0..6` | `v_t(2,1) = v_t(2) = 0,1,2,2,3,3,4` | equal at every `t`; values are not constant |
| same | `N = 6`, paper `d = 3`, `x = (3,2)`, `t = 0..6` | both sides `0,1,1,2,2,2,2` | |
| Theorem 1.1(ii) | `N = 7` (`M = 4`), `d = 2`, `j = 3` (`τ_3 = 7`), `x = (3,2)`, shift `1` | `v_t^{(7)}(3,2) = v_t^{(6)}(2,1) = 0,1,2,2,3,3,4,4,5,5`, `t = 0..9` | equal through `τ_3`, and beyond at this point |
| Corollary 1.1(ii) | `N = 7`, `d = 2`, `j = 3`, `x = (3,3) > M−j+1`, `t = 0..8` | `s_t^{(7)}(3,3) = s_t^{(6)}(2,2) = 4,4,2,4,2,2,4,0,4` | equal; differs from `s_0 = 4` at five times |
| Theorem 1.1(i), second display | `N = 5`, `x = (2)`; `v_9^{(2,5)}(2,2)` and `v_t^{(1,5)}(2)` for `t = 9,10,11` | `5` and `5,5,5` | terminal values finite and equal |
| Corollary 1.1(i) | `N = 5`, `x = (2)`, `t = 9` (stabilised) | `s(2,1) = 3`, `s(2) = 1` | `3 = 1 + 2` |
| Proposition 4.1, strong topple | `d = 2`, `M = 3` (`τ_2 = 3`); `max_{S_3}(v_{t+2} − v_t)`, `t = 0..5` | `2,2,1,1,1,1` | `≤ 1` for `t ≥ τ_2`; `= 2` before it, so the hypothesis is load-bearing |
| Proposition 4.1, strong derivative | `M = 3`, `i = 0`, `j = 1`: `v_t(1,1) − v_t(3,1)`, `t = 0..7` | `0,0,1,1,1,2,2,2` | `≤ 2`, attained at `t = 5, 6 < τ_3` |
| Proposition 4.1, strong derivative and strong facet | `M = 3`, `i = 1`, `j = 0`, `x = (2)`: `v_t` at `(2,1),(2,2),(2,3)`, `t = 0..9` | `(0,0,0),(1,1,1),(2,2,1),(2,2,2),(3,3,2),(3,3,2),(4,3,2),(4,4,2),(5,4,3),(5,5,3)` | derivative `≤ 2` at every `t`, the late regime `t ≥ τ_3 = 7` included since `i ≥ 1`; the gap `v(2,1) = v(2,2) + 1` at `t = 2, 6, 8` is followed each time by `(2,1)` staying and `(2,2)` rising by one |
| Proposition 4.1, self-similarity | `d = 2`, `M = 3`, `j = 2` (`τ_2 = 3`), `x = (2,2)` vs `(1,1)` on `C_4`, `t = 0..4` | `0,1,2,2,3` on both sides | equal through `τ_2` |
| Proposition 3.1 | `d_0 = 2`: pile `5` on `C_2^{(2)}`, pile `3` on `C_2^{(1)}`, `t = 0..3` | dimension 2: `0,1,1,1` at both sites; dimension 1: `0,1,2,2` | `v_∞ ≡ 1` against `v_∞ ≡ 2` |
| Proposition 3.2 | `d = 3`, pile `8` on `C_4`: `v_t(radial x)` for `x = 0..3`, and `a_t`, `t = 0..7` | `[0,0,0,0]/3, [1,1,1,1]/3, [2,2,2,1]/2, [3,3,2,2]/1, [4,3,3,2]/0, [4,4,3,2]/−1, [5,4,3,2]/−2, [5,4,3,2]/−3` | the block `x ≤ a_t` fires, `a_t < x ≤ a_{t−1}` holds still, the ripple moves out one site per step |
| `a_t`, `t_d`, `⌈√·⌉` | `d = 5`: `a_0..a_7`; `t_3, t_5, t_10`; `⌈√2⌉, ⌈√4⌉, ⌈√9⌉, ⌈√10⌉` | `5,5,4,2,1,0,−1,−2`; `3,3,4`; `2,2,3,4` | the paper's 781–790 |
| Lemma 3.1 | `d = 3`, `c = 8`, `t = 3`, `k = 1` | both sides `−5` | |
| corner value | `d = 2`, `M = 2, 3`, `t = 8` | `2, 3` | `= M`, as `aud_corner_terminal` proves in general |
| `S_M^{(d)}` enumeration | `|S_3^{(2)}|`, `|S_3^{(3)}|` | `6, 10` | the hand enumeration used for the maximum |

A further probe with kernel-checked `decide` witnesses and evaluations at larger times was
stopped by the auditor after 13 minutes, before it had printed; nothing from it is used here.

## 6. Reproduction

All probe files are in the auditor's scratch directory, outside the repository; what they
contain is described here so the run can be repeated.

```
git clone <repo> fresh && cd fresh && git checkout b0c8914
lake exe cache get && /usr/bin/time -v lake build DimRed      # exit 0, 8759 jobs, no warning
lake build Audit                                               # exit 0, 8751 jobs, 5 intentional sorry
bash Audit/check_standalone.sh --vocabulary                    # identical ×3, rc=0
bash Audit/check_standalone.sh Audit/<X>/Challenge.lean        # rc=0, one sorry warning per theorem
python3 tools/verify.py --keep-going                           # 15 gates OK
lake env lean AuditAxioms.lean                                 # 49 clean closures, 20 exprEq=true
lake env lean AuditWitness.lean                                # §5
```

`AuditAxioms.lean`: `import DimRed`; a command `#same_type a vs b` that resolves both names and
logs `ca.type == cb.type`; `#print axioms` on the 49 declarations listed in row 7;
`#same_type` on the 20 pairs; `#check @` on the 20 exports; `#print` on the 19 definitions of
§3.  `AuditWitness.lean`: the three theorems of §5 as written there, and the `#eval` lines
whose results are tabulated in §5.
