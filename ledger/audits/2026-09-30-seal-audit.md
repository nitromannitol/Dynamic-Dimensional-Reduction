# Seal audit, second key: the ten DRAFT_SORRY statements

Date: 2026-09-30.  Repository state: `faed57b` (clean tree).  Auditor: independent second key,
refute-first; did not write the statements or the proofs.  Procedure: `lean-statement-audit`
(pin, independent reconstruction from `paper/dimred.tex`, five-bin binder test, definition
bodies, ℕ∞/ℕ junk values, term-level consumption, axiom closure, seal simulation).

**Result: 10 of 10 not refuted.  9 PASS, 1 PASS-WITH-NOTE (strong derivative: the paper's
unbound `x` is fixed as `(x_i,1,1_j)`; this is the only true reading and the one the corrected
paper proves and uses).  No FAIL.  Four hygiene notes (H1-H4), none affecting a verdict.**

---

## G. Evidence shared by all ten nodes

All scratch files are in `scratch/audit/` (git-ignored), compiled with
`PATH=$HOME/.elan/bin:$PATH lake env lean scratch/audit/<f>.lean`.  SHA-256 of each file is in §R.

### G1. Pinning (recomputed independently)

- `paper/dimred.tex` sha256 `1423810f…12b3ef` = `source_pin.sha256`.
- For each of the ten nodes, the bytes strictly between the markers (one leading newline
  dropped, as in `leanform_tools.lean_source.block_body`) were re-hashed by my own script:
  **10/10 `HASH_OK`**, the declared theorem name equals the manifest `export`, exactly one marker
  pair per file, and the text after `FROZEN-STATEMENT-END` is exactly `:= by sorry`
  (state `DRAFT_SORRY`, `FROZEN_UNPROVED` today).
- Frozen tree ↔ manifest: the 20 files under `DimRed/Frozen/` and the 20 manifest `file:`
  entries coincide one-to-one.
- Manifest source ranges checked against the tex: 109/140 = `\begin{theorem}`/`\end{theorem}`,
  143/159 = corollary, 915-918, 919-926, 927-931, 932-940, 944-948 = the five items of
  `base_dimension` (preamble "For all M ≥ 2 and d ≥ 1" at 913).

### G2. Axiom closure (`SealAxioms.lean`)

Every one of the following prints exactly `[propext, Classical.choice, Quot.sound]`:
`reg_proved`, `reg_all`, `reg_induction`, `consist_step_of_earlier`, `facet_step_of_earlier`,
`topple_step_of_earlier`, and all ten bridges `base_dimension_{consistency,weak_compatibility,
strong_derivative,strong_compatibility,strong_topple}_of_reg`,
`{dimensional_reduction,terminal_dimensional_reduction,self_similarity,
sandpile_dimensional_reduction,sandpile_self_similarity}_of_reg`.
Control: `DimRed.Frozen.base_dimension_consistency` (still DRAFT) prints
`[propext, sorryAx, Classical.choice, Quot.sound]`, so the printer does distinguish.
The three step hypotheses are discharged by proofs, at their exact types:
`example : ConsistStepHyp := consist_step_of_earlier` (same for `FacetStepHyp`,
`ToppleStepHyp`) compiles; `reg_proved := reg_all consist_step_of_earlier facet_step_of_earlier
topple_step_of_earlier` has no hypotheses.  `grep` over `DimRed/` and the LatticeProb package:
no `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `admit`; the only
`sorry`s are the ten frozen bodies.

### G3. Term-level consumption and seal simulation

- `SealAxioms.lean`: for each node, `theorem audit_X : type_of% @DimRed.Frozen.X :=
  X_of_reg reg_proved` compiles (the type is read off the frozen export itself, not retyped),
  and each `audit_X` has clean axioms.
- `SealSim.lean`: the verbatim frozen bytes of all ten files (name changed to `SealSim.*`),
  elaborated in a file importing `DimRed.Support.RegProved`, proved by
  `by apply X_of_reg reg_proved <;> assumption`; a meta command compares the elaborated type
  with the DRAFT export's type: **exact `Expr` equality = true for all ten**, clean axioms.  So
  importing the proof chain does not change what the statement bytes mean.
- Import closure of `DimRed.Support.RegProved` (65 modules) contains no DRAFT frozen module (only
  the SEALED `Frozen.Prelim.{PtInd,ParabolicComparison,ToppleLimit,DifferenceComparison,
  AxisMonotonicity}`), so sealing the ten files by importing it creates no cycle.

### G4. Definition bodies (elaborated with `#print`, `SealAxioms.lean`)

| definition | body | against the paper |
|---|---|---|
| `inCube d N` | `∀ i, 1-⌊N/2⌋ ≤ x i ≤ ⌈N/2⌉` | tex:271-273: `N=2k`: `{x-k : 1≤x_i≤2k}` = `[1-k,k]`; `N=2k+1`: `{x+1 : |x_i|≤k}` = `[1-k,k+1]`. Match. |
| `sideHalf N` | `(N+1)/2` (ℕ floor) | `⌈N/2⌉`. Match for all `N`. |
| `inSimplex d M` | `(∀i, 1≤x i≤M) ∧ ∀ i≤j, x j ≤ x i` | `M ≥ x_1 ≥ … ≥ x_d ≥ 1`, index 0 = `x_1`. Match. |
| `lap`, `nbrSum` | `-(2d)·u x + Σ_i (u(x+e_i)+u(x-e_i))`, ℤ-valued `DimRed.nbrSum` (not the ℝ-valued `LatticeProb.nbrSum`) | tex:275-281 with zero padding (every `u` used vanishes off the cube). Match. |
| `odo` | `v_0=0`; on the cube `v_{t+1}=v_t+1{2d ≤ s₀+Δv_t}`, `0` off it | tex:100-107 with `s_t = s_0+Δv_t` (`sandp_succ`, `odo_succ_eq` prove the paper's two displays). Match. |
| `odoUnif`, `sandpUnif` | `s₀ ≡ 2d` in the dimension of the call | tex:39-41; each dimension its own `2d`. Match. |
| `odoInf` | `⨆ t, (v_t x).toNat` in ℕ∞ | `v_∞`; finiteness see G5. |
| `sandpInfUnif` | `2d + Δ(toNat ∘ odoInfUnif)` | `s_∞ = s_0 + Δv_∞`; `toNat` is the identity on finite values (G5). |
| `innerBoundary d N` | cube points with a neighbour off the cube | tex:130 `∂C`. Match. |
| `toppleTime d j` | `sInf {n ≥ 1 : ∃ x ∈ ∂C_{2j}, j ≤ v_n^{(d,2j)}(x)}` in ℕ∞ | tex:128 as corrected ("for some", CHANGES §1). Match. |
| `simplexMax d M f` | `sup'` over `simplex d M`, `0` if empty | `sup_{S_M}`; `S_M ≠ ∅` for `M ≥ 1`. Match. |
| `facetPoint x c j` | `Fin.append (Fin.snoc x c) 1_j` | `(x_i, c, 1_j)`, `c` at 1-indexed coordinate `i+1`. Match. |
| `Fin.snoc x c` | last coordinate `c` | `(x_{d-1}, c)`. Match. |

Decidable instances (`inCube`, `inSimplex`) are `Fintype.decidableForallFintype` and
`inferInstanceAs`; `simplex`/`innerBoundary` use `Classical.decPred`.  A `Decidable` instance
cannot change the truth of the Prop it decides, and no instance is custom-built.

### G5. ℕ∞ and ℕ junk values (`SealWitness.lean`, all clean axioms)

- `aud_toppleTime_ne_top : ∀ d j, 1 ≤ d → 1 ≤ j → toppleTime d j ≠ ⊤` (proved: `j = 1` from
  `v_1 ≡ 1`; `j ≥ 2` from `corner_reaches` fed by `reg_proved`).  So no hypothesis
  `τ ≤ t` (strong topple, late regime of the strong clauses) is vacuous by `⊤`, and no `t ≤ τ` is
  trivialised by `⊤`.  `toppleTime d 0 = ⊤` (empty cube) occurs only at `j = 0`, where
  `x > M - 0` contradicts `x ≤ M` in the paper too.  Measured: `τ_j = j(j-1)+1` for
  `d ≤ 3, j ≤ 6`, independent of `d`.
- `aud_odoInfUnif_ne_top : ∀ d N x, 1 ≤ d → odoInfUnif d N x ≠ ⊤` (proved via a uniform bound
  `v_t ≤ M(M+1)`: symmetric fold, `odoUnif_scale_of_reg`, `odo_le_oneDim`, `odoInf_one_eq`).
  The development also has `DimRed.odoInf_finite` (stabilisation, clean axioms), so the
  CORRESPONDENCE claim "finiteness is a theorem of the development" is true.  Hence `v_∞` and
  `s_∞` (whose `toNat` would otherwise be junk) are the paper's objects.
- Control: `odoInfUnif 0 5 ![] = ⊤` is proved (at `d = 0` every step topples); the frozen
  `hd : 1 ≤ d` (terminal: dimensions `d, d+1` with `d ≥ 1`) excludes it.
- ℕ subtraction: the only ones are `M - 1` in `toppleTime d (M-1)` (under `2 ≤ M`) and
  `d - 1` nowhere (the main theorems write the paper's `d` as `d+1`).  All shifts `M - j` are in ℤ.

### G6. Independent brute-force model (`sim.py`, `check10.py`)

A NumPy model written from the Lean bodies (not from the development's lemmas), cross-checked
against the compiled Lean definitions by `#eval` at 12 values (`EvalTest.lean`,
`SealWitness.lean`: all equal).  Exhaustive check of all ten statements, `d ≤ 4`, `M ≤ 7`
(Prop 4.1 on `C_{2M}`), every `N ≤ 14` (Thm 1.1 / Cor 1.1, odd and even), every `t` up to
stabilisation + 3:

| node | instances with all hypotheses true | non-trivial | failures |
|---|---:|---:|---:|
| consistency | 41 710 | 14 034 (j<M, t≥2, value ≥2) | 0 |
| weak | 924 | 924 (premise true) | 0 |
| strong-derivative | 14 652 (early 9 565, late 5 087) | 688 tight late, 169 tight early | 0 |
| strong-facet | 723 | 436 (late regime) | 0 |
| strong-topple | 417 | 321 (max = 1) | 0 |
| dimensional-reduction | 28 862 | 27 890 (value ≥2) | 0 |
| terminal | 406 | 406 | 0 |
| self-similarity | 31 548 | 13 433 (odd N, t≥2) | 0 |
| sandpile-reduction | 406 | 406 | 0 |
| sandpile-self-similarity | 16 892 | 12 930 (s_t ≠ 2d) | 0 |

Negative controls (hypotheses are load-bearing, not over-broad): with `i = 0` and `t ≥ τ_M`
(excluded by the regime) the strong derivative bound fails in 165 of 249 cases and the strong
facet conclusion in 165 of 201 (first: `d=1, M=2, t=4`, `v_4(1)-v_4(3) = 3`); strong topple before
`τ_{M-1}` fails in 84 of 304 cases (first: `d=1, M=2, t=0`, max 2).

---

## 1. prop-base-dimension-consistency — **PASS**

Source (tex:913, 915-918): for `M ≥ 2`, `d ≥ 1`, `1 ≤ j ≤ M`, `t ≤ τ_j`, `x ∈ S_M` with
`x > M-j`: `v_t^{(M)}(x) = v_t^{(j)}(x-(M-j))`, `v^{(M)}` on `C_{2M}`.

| binder | bin | citation |
|---|---|---|
| `d M : ℕ` | TYPING | tex:913 |
| `hd : 1 ≤ d`, `hM : 2 ≤ M` | SOURCE | tex:913 |
| `j`, `hj1 : 1 ≤ j`, `hj2 : j ≤ M` | SOURCE | tex:915 |
| `t`, `ht : ↑t ≤ toppleTime d j` | SOURCE | tex:915, τ_j tex:128 (CHANGES §1) |
| `x : Site d`, `hx : inSimplex d M x` | SOURCE | tex:428-436 (domain `S_M`) |
| `hxgt : ∀ i, ↑M - ↑j < x i` | SOURCE | tex:917 |

SOURCE 7, STANDING 0, TYPING 1, RULED 0, EXCESS 0.  Conclusion `odoUnif d (2M) t x =
odoUnif d (2j) t (x - (M-j))` in ℤ.  Range: identical (includes the trivial `j = M`, as the
paper does).  Witness (kernel `decide`): `d=2, M=3, j=2, t=3 = τ_2` (proved `toppleTime 2 2 = 3`),
`x=(2,2)`: both sides `= 2`, at the top of the time window.

## 2. prop-base-dimension-weak — **PASS**

Source (tex:919-926, conclusion as corrected by CHANGES §6; the arXiv text was a tautology).

| binder | bin | citation |
|---|---|---|
| `M`, `i`, `j` (dimension `i+1+j`) | TYPING/SOURCE | tex:919 `i+j+1=d` |
| `hM : 2 ≤ M` | SOURCE | tex:913 |
| `t`, `ht : 1 ≤ t` | SOURCE | tex:919 |
| `x : Fin i → ℤ`, `hx2 : ∀ a, 2 ≤ x a` | SOURCE | tex:919 `x_i ≥ 2` |
| `hxs : inSimplex (i+1+j) M (facetPoint x 1 j)` | SOURCE | tex:428-436 |
| `h` (the premise) | SOURCE | tex:922 |

EXCESS 0.  `d ≥ 1` automatic.  Witness: `M=2, i=1, j=0, t=3, x=(2)`: premise
`v_3(2,1)=2 = v_3(2,2)+1` true, conclusion `v_4(2,1)=v_3(2,1)=2`.

## 3. prop-base-dimension-strong-derivative — **PASS-WITH-NOTE**

Source (tex:927-931): for `x_i ≥ 2`, `j ≥ 0`, `i < d`, (`t < τ_M`, `i ≥ 0`) or (`i ≥ 1`,
`t ≥ τ_M`): `v_t(x) - v_t(x + 2e_{i+1}) ≤ 2`, with bold `x` unbound.

| binder | bin | citation |
|---|---|---|
| `M`, `i`, `j` (dimension `i+1+j`) | TYPING/SOURCE | tex:927 |
| `hM : 2 ≤ M` | SOURCE | tex:913 |
| `t`, `x : Fin i → ℤ`, `hx2` | SOURCE | tex:927 |
| `hxs` | SOURCE | tex:428-436 |
| `hreg : ↑t < τ_M ∨ (1 ≤ i ∧ τ_M ≤ ↑t)` | SOURCE | tex:928 verbatim |

EXCESS 0.  **Note (the reading).**  Lean fixes `x = (x_i, 1, 1_j)`, so `x + 2e_{i+1} =
(x_i, 3, 1_j)`.  Refutation attempt of this reading failed; evidence it is the faithful one:
(a) the quantifier "for all `x_i ≥ 2`, `j ≥ 0`" binds exactly the head and tail of the
facet point used in the companion display 932-940 under the same preamble; (b) the paper's
use is `eq:two_derivative_bound` (tex:1263-1265), literally `(x_{i-1},1,1_j)` vs
`(x_{i-1},3,1_j)` (index shift `i-1 ↔ i` of Section 5); (c) the `d = 1` proof says "taking
`x = 1`" (tex:1025-1029); (d) CHANGES §9 (documented correction) states "Bound 5 at the point
`(x_{i-1}, 1, 1_j)` ... is the clause"; (e) Section 5 closes Case 2 with "Bound 5 at `(x_{i-1},1,1_j)` ... is
`eq:two_derivative_bound`" (tex:1429-1430); (f) the broader reading "all `x ∈ S_M`" is **false**:
`d=1, M=4, t=9 < τ_4=13`, `x=2`: `v_9(2) - v_9(4) = 6 - 3 = 3 > 2` (also `d=2,3` at `(2,1)`,
`(2,1,1)`).  Where `(x_i,3,1_j)` is unsorted (some head entry `= 2`) or off the cube (`M = 2`),
Lean evaluates the cube odometer (symmetric extension, zero padding) — the paper's own
convention; this makes Lean at least as strong, and it is proved.  Recommendation: record the
disambiguation as a ruling in `ledger/decisions.md` (readings.yaml marks it FLAGGED but no
decision entry exists).  Witnesses: early `M=3, i=0, j=1, t=5` (`5 < τ_3` proved from
`6 ≤ τ_3`): `v(1,1) - v(3,1) = 4 - 2 = 2` (tight); late `M=2, i=1, j=0, t=3 = τ_2`, `x=(2)`:
`2 - 0 = 2` (tight, off-cube point); in-cube late `M=3, t=7=τ_3, x=(2)`: `4 - 2 = 2` (`#eval`).

## 4. prop-base-dimension-strong-facet — **PASS**

Source (tex:932-940; hypothesis subscript corrected by CHANGES §7).  Binders as node 3 plus
`h` (premise, tex:935): EXCESS 0; the two conjuncts are the two lines of the aligned display in
order.  Witnesses (kernel): early `M=2, i=0, j=1, t=2 < τ_2=3`: `v_2(1,1)=2=v_2(2,1)+1`, then
`v_3(1,1)=2`, `v_3(2,1)=2`; late `M=2, i=1, j=0, t=3=τ_2, x=(2)`: premise `2=1+1`, then
`v_4(2,1)=2`, `v_4(2,2)=2`.  `#eval`: `M=3, t=7, x=(3)`: `(3,2) → (3,3)`.

## 5. prop-base-dimension-strong-topple — **PASS**

Source (tex:944-948).  Binders `d M hd hM` (SOURCE tex:913), `t`, `ht : τ_{M-1} ≤ ↑t` (SOURCE
tex:945).  EXCESS 0.  `M - 1 ≥ 1` under `hM`; `τ_{M-1} < ⊤` (G5) so the hypothesis is
satisfiable.  Witness (kernel): `d=2, M=3, t=3=τ_2`: `simplexMax = 1` exactly (the bound is
attained at `(1,1)`: `v_5 - v_3 = 4 - 3`).

## 6. thm-dimensional-reduction — **PASS**

Source (tex:109-117): `N ≥ 1`, `d ≥ 2`, `M=⌈N/2⌉`, `t ≥ 1`, `x_{d-1} ∈ S_M^{(d-1)}`:
`v_t^{(d,N)}(x_{d-1},1) = v_t^{(d-1,N)}(x_{d-1})`.  Lean writes `d+1` for `d`.  Binders
`N d hN hd t ht x hx`: all SOURCE, EXCESS 0.  Range identical, every `N ≥ 1` (odd `N` and
`M = 1` handled in the bridge, not excluded).  Witness (kernel): `N=5` (odd), paper `d=2`,
`t=3`, `x=(2)`: both sides `= 2`.

## 7. thm-terminal-reduction — **PASS**

Source (tex:118-121): for `x_{d-1} ≥ 2` (domain `S_M^{(d-1)}` inherited from the preceding
display): `v_∞^{(d,N)}(x_{d-1},2) = v_∞^{(d-1,N)}(x_{d-1})`.  Binders `N d hN hd x hx hx2`:
SOURCE (hx by context), EXCESS 0.  Carrier ℕ∞, both sides finite (G5), so the equation is the
paper's, not `⊤ = ⊤`; the bridge proves it by interleaving `v_t(x,2) ≤ v_t(x,1) ≤ v_{t+1}(x,2)`,
not by junk.  Vacuous for `N ≤ 2` exactly as in the paper (`x ≥ 2` impossible in `S_1`).
Witness: `N=5`, `x=(2)`: equality applied, `2 ≤ v_∞^{(1,5)}(2) ≠ ⊤` (value 5 at stabilisation,
`#eval`).

## 8. thm-self-similarity — **PASS**

Source (tex:122-130): `j < M`, `t ≤ τ_j`, `x ∈ S_M^{(d)}`, `x > M-j`, `d ≥ 2`.  Binders
`N d hN hd j hj t ht x hx hxgt`: SOURCE, EXCESS 0.  `j = 0` is vacuous in both (as readings
say).  Witness (kernel): `N=5` (odd), `d=2`, `j=2`, `t=3=τ_2`, `x=(2,2)`: both `= 2`.  `#eval`:
`N=7, j=3, t=7=τ_3, x=(3,2)`: both `= 4`.

## 9. cor-sandpile-reduction — **PASS**

Source (tex:147-151).  Binders `N d hN hd x hx hx2`: SOURCE, EXCESS 0.  `sandpInfUnif` reads
`v_∞` through `toNat`; G5 proves every `v_∞` finite for `d ≥ 1`, so no junk `0` enters the
Laplacian.  Witness: `N=5`, `x=(2)`: statement applied, plus finiteness of `v_∞` at every site in
both dimensions; values `s_∞(2,1) = 3 = 1 + 2` (`#eval` at stabilisation `T=9`).

## 10. cor-sandpile-self-similarity — **PASS**

Source (tex:153-156; threshold `M-j+1`).  Binders as node 8 with `hxgt : M-j+1 < x i`:
SOURCE, EXCESS 0.  Witness (kernel): `N=7, d=2, j=3, t=2 ≤ τ_3, x=(3,3)`: both `= 2 ≠ s_0 = 4`.

---

## H. Hygiene notes (no verdict impact)

- **H1.** `DimRed/Support/TerminalReduction.lean:8` imports the DRAFT module
  `DimRed.Frozen.Main.TerminalReduction` but uses no DRAFT export (only the SEALED
  `Frozen.parabolic_comparison`; `odoInf_finite` has clean axioms).  Against the letter of the
  draft-quarantine rule; drop the import.  It is outside the `RegProved` closure, so no cycle.
- **H2.** Sealing must change each frozen file's import line (`DimRed.Support.Recursion` →
  a module exporting `reg_proved` and the bridges, e.g. `DimRed.Support.RegProved`) besides the
  body.  G3 shows the frozen bytes elaborate to the identical `Expr` in that context; the seal
  reviewer should expect exactly `import` + body in the diff, and the frozen hashes unchanged.
- **H3.** The regime binder of nodes 3-4 is named `hreg`, the same name as the bridges'
  induction hypothesis.  Naming only.
- **H4.** `hN : 1 ≤ N` is unused (`_hN`) in the self-similarity and terminal bridges.  It is a
  paper premise; harmless.

## R. Reproduction

```
cd /home/bourabbe/lean/Dynamic-Dimensional-Reduction
PATH=$HOME/.elan/bin:$PATH lake env lean scratch/audit/SealAxioms.lean   # G2, G3, G4  (~25 s)
PATH=$HOME/.elan/bin:$PATH lake env lean scratch/audit/SealSim.lean      # G3 seal simulation
PATH=$HOME/.elan/bin:$PATH lake env lean scratch/audit/SealWitness.lean  # G5, witnesses (~3.5 min)
cd scratch/audit && python3 check10.py 4 7                               # G6 (~20 s)
```

```
b330481678845355f07df8e1395c3ab01d21253fd99495dc11a377dad60336a9 SealAxioms.lean
761cb3be7a63d995c3ca0aa4dde43221fdd65646478f2716811fc3511c229b31 SealSim.lean
bbf5d0902bb69fa1cb3779b870c948699e5dcab0b66d2a0d55f0c77f438c130d SealWitness.lean
2dabe8e7bfc004a9c0741f29bbb53c69b2f4cf270ae023fc8c2dec93bfb21b69 EvalTest.lean
ab261ae89a0e1b0233d702f7505553ed158856b60af6968f80dd02f531a2d77c AxCorner.lean
90f858ba5dd554e4f533ad974613cb6f1d06b99d71eac675a628ed66246f53d3 AxFinite.lean
2fa174c0ca15b9a760cc6e6e7dc376161a3bb5036f5a1273e8605adb015ac1d9 sim.py
32fd1f848820a60f5bef1b4854bec7459f0208041630159ff23fdc4b773b64de check10.py
```
