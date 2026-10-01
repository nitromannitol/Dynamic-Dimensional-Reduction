# Extended refute-first check of the ten frozen statements

Date: 2026-10-01.  Auditor: second key, refute-first, reading only the model and the
statements (not the development's proofs).  This extends the independent brute-force check of
[`2026-09-30-seal-audit.md`](2026-09-30-seal-audit.md) §G6 from `d ≤ 4, M ≤ 7` to
`d ≤ 4, M ≤ 8` and adds `d ≤ 5, M ≤ 6`.

**Result: all ten nodes have zero failures in both runs.  The hypothesis-free negative
controls still fail, so the hypotheses remain load-bearing.  No statement is refuted.**

## The model

The model and the checker are unchanged from the seal audit; their SHA-256 are exactly the
audit's, so the comparison is direct:

```
2fa174c0ca15b9a760cc6e6e7dc376161a3bb5036f5a1273e8605adb015ac1d9 sim.py
32fd1f848820a60f5bef1b4854bec7459f0208041630159ff23fdc4b773b64de check10.py
```

They live in the working tree under `scratch/audit/` (not tracked, as for the seal audit).
`sim.py` is an independent NumPy model written from the Lean bodies; `check10.py` quantifies
each frozen statement over the model and reports instances / non-trivial instances /
failures.

## Reproducing

```
cd scratch/audit
python3 check10.py 4 8     # d ≤ 4, M ≤ 8; every N ≤ 16
python3 check10.py 5 6     # d ≤ 5, M ≤ 6; every N ≤ 12
```

## Node counts

`inst` is the number of parameter tuples with all hypotheses true, `nontriv` the number that
also exercise the conclusion non-trivially, and `FAIL` the number of failures.  The excluded
and `before-tau` rows are the deliberate negative controls: they drop a hypothesis and are
*expected* to fail, which is what shows the hypotheses are not vacuous.

| node | `4 8` inst | nontriv | FAIL | `5 6` inst | nontriv | FAIL |
|---|---:|---:|---:|---:|---:|---:|
| consistency | 95 578 | 37 206 | 0 | 33 256 | 8 398 | 0 |
| weak | 1 405 | 1 405 | 0 | 871 | 871 | 0 |
| strong-deriv | 27 557 | 1 010 | 0 | 16 634 | 767 | 0 |
| strong-facet | 1 153 | 704 | 0 | 671 | 446 | 0 |
| strong-topple | 540 | 428 | 0 | 395 | 295 | 0 |
| dimred | 54 342 | 52 932 | 0 | 32 668 | 31 104 | 0 |
| terminal | 644 | 644 | 0 | 492 | 492 | 0 |
| selfsim | 80 580 | 35 967 | 0 | 20 752 | 8 142 | 0 |
| sandpile-red | 644 | 644 | 0 | 492 | 492 | 0 |
| sandpile-selfsim | 46 380 | 36 788 | 0 | 9 228 | 6 876 | 0 |
| **negative controls (expected failures)** | | | | | | |
| strong-deriv-excluded (i = 0, t ≥ τ_M) | 316 | 316 | 204 | 245 | 245 | 170 |
| strong-facet-excluded | 252 | 252 | 204 | 200 | 200 | 170 |
| strong-topple-before-tau | 476 | 476 | 112 | 225 | 225 | 75 |

The first failures of the controls match the seal audit (`d = 1, M = 2, t = 4` for the two
excluded rows), so the extension has not shifted the model.

## Scope

This is a strengthening of the evidence, not a replacement for the seal audit or for the
Lean proofs.  The statements are still certified by the joint induction `DimRed.reg_proved`
with axiom closure `{propext, Classical.choice, Quot.sound}`; the model check is what makes a
false or vacuous statement at small parameters unlikely to have slipped through.
