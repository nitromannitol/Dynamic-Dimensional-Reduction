import DimRed.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the ten proved results restated in
`DimRed/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

None of the paper's main results is proved yet, so none is printed here: the frozen
statements of Theorem 1.1 and Corollary 1.1 still depend on `sorryAx`.
`python3 tools/check_axioms.py` prints the axiom closure of all twenty registered
statements, open ones included.

Nothing is assumed in this development: no theorem takes a cited result as a hypothesis,
and no `axiom` is declared.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build DimRed.Meta.AxiomsAudit`).
-/

#print axioms DimRed.pt_ind_lemma
#print axioms DimRed.parabolic_comparison
#print axioms DimRed.symmetry_lemma
#print axioms DimRed.general_difference_comparison
#print axioms DimRed.axis_monotonicity
#print axioms DimRed.derivative_bound
#print axioms DimRed.topple_limit
#print axioms DimRed.no_reduction_at_critical_dimension
#print axioms DimRed.radial_laplacian
#print axioms DimRed.base_case
