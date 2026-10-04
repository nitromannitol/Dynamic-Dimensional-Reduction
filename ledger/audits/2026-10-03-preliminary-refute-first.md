# Refute-first audit of the ten preliminary registered nodes

Date: 2026-10-03.  Auditor: independent second key, refute-first, reading only the paper's
statements and the model, not the development's proofs.  This is the audit required to promote
the ten preliminary Section 2 and 3 nodes from `SEALED` to `PROVED`; the other ten (Theorem
1.1, Corollary 1.1 and Proposition 4.1) have the audit of
[`2026-09-30-seal-audit.md`](2026-09-30-seal-audit.md), extended by
[`2026-10-01-extended-refutation.md`](2026-10-01-extended-refutation.md).

**Result: none of the ten is refuted.**  Nine statements were checked exhaustively on the
small-parameter model `d ≤ 3, M = 3` and the tenth on 80 460 boundary instances of its paper
use; every check had zero failures.  All twenty frozen declarations additionally pass the
`check_axioms` gate, whose closures are exactly `{propext, Classical.choice, Quot.sound}`.

## The model

`sim.py` is the NumPy model of `DimRed/Support/Basic.lean` used by the seal audit;
`check_prelim.py` adds a general-pile odometer `odo_gen`, the cube symmetry `cubeSym`, the
radial points, `blockEdge`, `tCrit` and `cornerPoint`.  Both live in `scratch/audit/`
(untracked).  Each statement is read off its frozen marker and checked directly, with the
hypotheses of the frozen statement as stated.

```
cd scratch/audit
python3 check_prelim.py 3 3     # nine statements, d ≤ 3, M = 3
python3 check_diffcomp.py      # general_difference_comparison, n = 1, w = 2e_0, g = 2x_0
```

## Counts (`check_prelim.py 3 3`)

`inst` is the number of parameter tuples with all hypotheses true; `FAIL` the number of
failures.  Nothing above zero appears.

| node | check | inst | FAIL |
|---|---|---:|---:|
| `lem-pt-ind` | `odo(t+1,x) = floor((s_0 x + nbrSum v_t x)/2d)` | 6 240 | 0 |
| `lem-symmetry` | `v_t(σx) = v_t(x)` for symmetric `s_0`, all `σ` | 1 518 864 | 0 |
| `lem-radial-laplacian` | the radial Laplacian identity on `C_4` | 608 | 0 |
| `lem-topple-limit` | `max(v_{t+j}-v_t) ≤ max(v_{t_0+j}-v_{t_0})` | 307 248 | 0 |
| `prop-no-reduction` | terminal values `1` and `2` at the critical dimension | 42 | 0 |
| `prop-base-case` | the block display and the ripple display on `C_4` | 38 | 0 |
| `cor-axis-monotonicity` | the single-step monotonicity | 2 620 | 0 |
| `cor-derivative-bound` | `v_t(x)-v_t(x+e_j) ≤ k·x_j` under the corner bound | 13 083 | 0 |
| `lem-parabolic-comparison` | the local inequality `(-2d v_{t+1}+nbrSum v_t)+s_0 ≤ 2d-1` | 5 328 | 0 |
| `lem-difference-comparison` | see below: the paper use, 80 460 instances | 80 460 | 0 |

## `general_difference_comparison`

The statement is a maximum principle quantified over a step family `w`, a superharmonic `g`
and a boundary hypothesis, so it is not exhausted by the small-parameter sweep.  The check
`check_diffcomp.py` takes the paper's own use (`n = 1`, `w = 2 e_0`, `g(x) = 2 x_0`, which is
superharmonic because `nbrSum g = 2d·g`), searches `t_0 ≤ 11` and `c ∈ [0, 4d-1]` for the
initial condition, verifies the boundary hypothesis for every time and boundary point, and
then checks the conclusion: **80 460 instances, 0 failures**.  A full refutation of the general
statement is not attempted; what is checked is that its paper use is not refuted and that the
boundary hypothesis is satisfiable.

## Axiom closure and readings

`python3 tools/verify.py` reports the twenty frozen declarations' closures are exactly
`{propext, Classical.choice, Quot.sound}`.  The clause readings of all twenty nodes are
recorded in [`../readings.yaml`](../readings.yaml) and enforced by `check_clauses`,
`check_exponents`, `paper_anchors` and `paper_citations`; the preliminary ten were additionally
audited against the paper during the freeze (the transcription repair recorded in the README's
build history).

## Conclusion

Together with the seal audit of the ten regularity/main statements, every `SEALED` node now has
a recorded independent refute-first audit, so the twenty nodes are promoted to `PROVED` in
`ledger/manifest.yaml`.
