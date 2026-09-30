import DimRed.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the twenty proved results restated in
`DimRed/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

`python3 tools/verify.py` (the check_axioms gate) prints the axiom closure of all twenty
registered statements.

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
#print axioms DimRed.dimensional_reduction
#print axioms DimRed.terminal_dimensional_reduction
#print axioms DimRed.self_similarity
#print axioms DimRed.sandpile_dimensional_reduction
#print axioms DimRed.sandpile_self_similarity
#print axioms DimRed.base_dimension_consistency
#print axioms DimRed.base_dimension_weak_compatibility
#print axioms DimRed.base_dimension_strong_derivative
#print axioms DimRed.base_dimension_strong_compatibility
#print axioms DimRed.base_dimension_strong_topple
