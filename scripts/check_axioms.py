#!/usr/bin/env python3
"""Require one exact standard-axiom report for each result restated in DimRed/MainTheorems.lean
and for each definitional statement of DimRed/Frozen/Definitions/.

    lake build DimRed.Meta.AxiomsAudit 2>&1 | tee axioms-audit.log
    python3 scripts/check_axioms.py axioms-audit.log
"""
import pathlib
import re
import sys

expected = {
    'DimRed.pt_ind_lemma',
    'DimRed.parabolic_comparison',
    'DimRed.symmetry_lemma',
    'DimRed.general_difference_comparison',
    'DimRed.axis_monotonicity',
    'DimRed.derivative_bound',
    'DimRed.topple_limit',
    'DimRed.no_reduction_at_critical_dimension',
    'DimRed.radial_laplacian',
    'DimRed.base_case',
    'DimRed.dimensional_reduction',
    'DimRed.terminal_dimensional_reduction',
    'DimRed.self_similarity',
    'DimRed.sandpile_dimensional_reduction',
    'DimRed.sandpile_self_similarity',
    'DimRed.base_dimension_consistency',
    'DimRed.base_dimension_weak_compatibility',
    'DimRed.base_dimension_strong_derivative',
    'DimRed.base_dimension_strong_compatibility',
    'DimRed.base_dimension_strong_topple',
    'DimRed.strict_head_facet',
    'DimRed.one_terminal_profile',
    'DimRed.one_terminal_derivative',
    'DimRed.terminal_odometer_finite',
    'DimRed.Frozen.folded_lift_definition',
    'DimRed.Frozen.folded_neighbors_definition',
    'DimRed.Frozen.folded_odometer_definition',
    'DimRed.Frozen.pile_definition',
    'DimRed.Frozen.terminal_pile_characterization',
    'DimRed.Frozen.maximum_definition',
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
log = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'warning:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
    raise SystemExit('Axiom audit emitted a warning or reported sorryAx')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
seen = set()
for theorem, axioms in reports:
    if theorem not in expected or theorem in seen:
        raise SystemExit('Unexpected or duplicate axiom report: ' + theorem)
    actual = [a.strip() for a in axioms.split(',')]
    if len(actual) != 3 or set(actual) != standard:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + axioms)
    seen.add(theorem)
if seen != expected:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(expected - seen)))
print('All %d results use exactly propext, Classical.choice and Quot.sound.' % len(expected))
