module

public import DimRed.MainTheorems
public import DimRed.Frozen.Definitions.FoldedLift
public import DimRed.Frozen.Definitions.FoldedNeighbors
public import DimRed.Frozen.Definitions.FoldedOdometer
public import DimRed.Frozen.Definitions.Pile
public import DimRed.Frozen.Definitions.TerminalPile
public import DimRed.Frozen.Definitions.Maximum

@[expose] public section

/-!
# Axioms audit

Building this module prints the axiom dependencies of the results restated in
`DimRed/MainTheorems.lean` and of the six definitional statements of `DimRed/Frozen/Definitions/`.
Each must report exactly the three standard foundational axioms of Mathlib: `propext`,
`Classical.choice`, `Quot.sound`; `scripts/check_axioms.py` checks the report against an explicit
list of theorems.

`python3 tools/verify.py`, through its axiom check, prints the axiom closure of every
statement recorded in `ledger/manifest.yaml`.

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

#print axioms DimRed.strict_head_facet
#print axioms DimRed.one_terminal_profile
#print axioms DimRed.one_terminal_derivative
#print axioms DimRed.terminal_odometer_finite

#print axioms DimRed.Frozen.folded_lift_definition
#print axioms DimRed.Frozen.folded_neighbors_definition
#print axioms DimRed.Frozen.folded_odometer_definition
#print axioms DimRed.Frozen.pile_definition
#print axioms DimRed.Frozen.terminal_pile_characterization
#print axioms DimRed.Frozen.maximum_definition
