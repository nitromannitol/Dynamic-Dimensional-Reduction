module

public import DimRed.Meta.AxiomsAudit

@[expose] public section

#print DimRed.Frozen.base_dimension_weak_compatibility
#print axioms DimRed.Frozen.base_dimension_weak_compatibility
#print DimRed.Frozen.dimensional_reduction
#print axioms DimRed.Frozen.dimensional_reduction
#print DimRed.Frozen.terminal_dimensional_reduction
#print axioms DimRed.Frozen.terminal_dimensional_reduction
#print DimRed.Frozen.sandpile_dimensional_reduction
#print axioms DimRed.Frozen.sandpile_dimensional_reduction
#print DimRed.Frozen.symmetry_lemma
#print axioms DimRed.Frozen.symmetry_lemma
#print DimRed.Frozen.no_reduction_at_critical_dimension
#print axioms DimRed.Frozen.no_reduction_at_critical_dimension
#print DimRed.Frozen.radial_laplacian
#print axioms DimRed.Frozen.radial_laplacian
#print DimRed.Frozen.pt_ind_lemma
#print axioms DimRed.Frozen.pt_ind_lemma
#print DimRed.Frozen.parabolic_comparison
#print axioms DimRed.Frozen.parabolic_comparison
#print DimRed.Frozen.general_difference_comparison
#print axioms DimRed.Frozen.general_difference_comparison
#print DimRed.Frozen.base_case
#print axioms DimRed.Frozen.base_case
#print DimRed.Frozen.base_dimension_consistency
#print axioms DimRed.Frozen.base_dimension_consistency
#print DimRed.Frozen.base_dimension_strong_derivative
#print axioms DimRed.Frozen.base_dimension_strong_derivative
#print DimRed.Frozen.base_dimension_strong_compatibility
#print axioms DimRed.Frozen.base_dimension_strong_compatibility
#print DimRed.Frozen.base_dimension_strong_topple
#print axioms DimRed.Frozen.base_dimension_strong_topple
#print DimRed.Frozen.self_similarity
#print axioms DimRed.Frozen.self_similarity
#print DimRed.Frozen.sandpile_self_similarity
#print axioms DimRed.Frozen.sandpile_self_similarity
#print DimRed.Frozen.axis_monotonicity
#print axioms DimRed.Frozen.axis_monotonicity
#print DimRed.Frozen.derivative_bound
#print axioms DimRed.Frozen.derivative_bound
#print DimRed.Frozen.strict_head_facet
#print axioms DimRed.Frozen.strict_head_facet
#print DimRed.Frozen.one_terminal_profile
#print axioms DimRed.Frozen.one_terminal_profile
#print DimRed.Frozen.one_terminal_derivative
#print axioms DimRed.Frozen.one_terminal_derivative
#print DimRed.Frozen.folded_lift_definition
#print axioms DimRed.Frozen.folded_lift_definition
#print DimRed.Frozen.folded_neighbors_definition
#print axioms DimRed.Frozen.folded_neighbors_definition
#print DimRed.Frozen.folded_odometer_definition
#print axioms DimRed.Frozen.folded_odometer_definition
#print DimRed.Frozen.pile_definition
#print axioms DimRed.Frozen.pile_definition
#print DimRed.Frozen.terminal_pile_characterization
#print axioms DimRed.Frozen.terminal_pile_characterization
#print DimRed.Frozen.maximum_definition
#print axioms DimRed.Frozen.maximum_definition
#print DimRed.Frozen.topple_limit
#print axioms DimRed.Frozen.topple_limit
#print DimRed.Corrected.CubeSite
#print axioms DimRed.Corrected.CubeSite
#print DimRed.Corrected.SimplexSite
#print axioms DimRed.Corrected.SimplexSite
#print DimRed.Corrected.pile
#print axioms DimRed.Corrected.pile
#print DimRed.Corrected.terminalPile
#print axioms DimRed.Corrected.terminalPile
#print DimRed.Corrected.maximum
#print axioms DimRed.Corrected.maximum
#print DimRed.foldedLift
#print axioms DimRed.foldedLift
#print DimRed.foldedNbrSum
#print axioms DimRed.foldedNbrSum
#print DimRed.foldedOdo
#print axioms DimRed.foldedOdo
#print DimRed.odoInfUnif
#print axioms DimRed.odoInfUnif
#print DimRed.Corrected.odoInfUnif_ne_top
#print axioms DimRed.Corrected.odoInfUnif_ne_top
#print DimRed.Corrected.terminalPile_eventually
#print axioms DimRed.Corrected.terminalPile_eventually
#print DimRed.Corrected.terminalPile_eventually_cube_site
#print axioms DimRed.Corrected.terminalPile_eventually_cube_site

example (d N : ℕ) (hd : 1 ≤ d) (y : LatticeProb.Site d) :
    DimRed.odoInfUnif d N y ≠ ⊤ :=
  DimRed.Corrected.odoInfUnif_ne_top d N hd y

example (d N : ℕ) (hd : 1 ≤ d) (x : DimRed.Corrected.CubeSite d N) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      DimRed.Corrected.terminalPile d N hd x =
        DimRed.Corrected.pile d N (fun _ => 2 * (d : ℤ)) t x :=
  DimRed.Corrected.terminalPile_eventually d N hd x

example : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
    DimRed.Corrected.terminalPile 2 4 (by norm_num) ⟨![1, 1], by decide⟩ =
      DimRed.Corrected.pile 2 4 (fun _ => 2 * ((2 : ℕ) : ℤ)) t ⟨![1, 1], by decide⟩ :=
  DimRed.Corrected.terminalPile_eventually_cube_site
