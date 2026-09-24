# Audit Comparator Surface

This directory will hold Mathlib-only comparator challenges for the main theorems of the
formalization of *Dynamic dimensional reduction in the Abelian sandpile* (Ahmed Bou-Rabee),
in the form used by the repositories this one follows: for each main theorem, a
`Challenge.lean` that imports only `Mathlib`, rebuilds from scratch every definition needed
to read the theorem, states it, and ends with one intentional `sorry`; a `Solution.lean`
that fills it from the library; and a `comparator.json` for
[`leanprover/comparator`](https://github.com/leanprover/comparator), which checks that the
two statements have identical elaborated types and that the proof reduces to the three
standard axioms.

**It holds none yet.**  None of the paper's main results is proved: Theorem 1.1
(dimensional reduction and self-similarity) and Corollary 1.1 (their consequences for the
sandpile) are registered as frozen statements whose proofs are still open, together with
the five clauses of Proposition 4.1 that the paper proves with them by one joint induction.
A challenge whose solution rests on a `sorry` would certify nothing, so the challenges will
be added when the main theorems are sealed.  Until then there is no `Audit` library in
`lakefile.lean` and no comparator workflow.

What is proved so far, the results of Sections 2 and 3 of the paper, is restated in full in
[`DimRed/MainTheorems.lean`](../DimRed/MainTheorems.lean), and
[`DimRed/Meta/AxiomsAudit.lean`](../DimRed/Meta/AxiomsAudit.lean) prints the axioms of each.
