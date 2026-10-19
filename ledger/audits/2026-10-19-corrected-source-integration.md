# Corrected arXiv-format source integration, 19 October 2026

The manifest selects `paper/corrected-arxiv/dimred-corrected-arxiv.tex`, SHA-256
`217e1e34369afdd0342c47560d04e85042a67da8a6b2f397e0644cd2dc9fc121`, with its
bibliography and figure inputs. It applies corrections C01–C25, listed with their
reasons in `paper/corrected-arxiv/SOURCE_NOTE.md`, and a C18 proof-description
refinement that matches the joint induction and removes a duplicated heading.

The official `paper/dimred-arxiv.tex` remains
`7b47485ebc0b16b08be0ed91b360ec9b1b06f5a9bba6ffca93ededeaa09d9823`;
the historical local `paper/dimred.tex` remains
`1423810fa6c1469dbec2a1ba633652946a467297bfab3ea4d89cbd3b1e12b3ef`.
The abstract is byte-identical. The unversioned arXiv link identifies v2,
revised 29 December 2021. The corrected TeX builds to 23 pages without
unresolved references or citations.

## Source checks

C14's block and ripple arithmetic was re-derived independently: the edge excess
is `-1-(t-1)x`, and the early floor overshoot and late quadratic inequality give
the remaining block branches. The moving-front and adjacent-window identities
agree with `block_eq`, `beyond_block_eq` and `ripple_shift`, and a radial replay
through dimension 128 found no failure. C09 is backed by
`DimRed.Corrected.axis_monotonicity`, which has no height hypothesis.

## Statements

All twenty inherited rows have corrected-source successors. Ten statements change;
ten keep their exact statement bytes while their versions and source addresses
advance. Three added clauses register the strict-head C/S facet lemma and the
one-dimensional terminal profile with its full endpoint derivative. Six units
record the defining equations of the repaired definitions (folded lift, folded
neighbor sum, folded odometer, physical pile, terminal pile, nonempty maximum);
they add no numbered-theorem coverage. All fifteen theorem-like environments of
the corrected source are addressed.

Two scope conventions are deliberate: the derivative bound is stated on the
fundamental domain `S_M`, the section's convention, and the topple contraction
assumes `1 ≤ M` so that its maximum ranges over a nonempty domain.

The weak topple contraction uses `DimRed.Corrected.topple_limit` from
`DimRed/Support/ToppleContractionFull.lean`, with cube-local symmetry, a genuine
nonempty maximum and no height bound. Existing bounded floor consumers use the
proved `bounded_point_update` specialization; no lower-height premise is added to
a signed source statement.

## Review and checks

An independent review compared every changed statement, new unit and source
change with the corrected TeX. It found two problems, both fixed before landing:
the Frozen file headers had lost their quotation of the source statement, and
the terminal-pile unit asserted finiteness and stabilization at an address that
only defines the pile. The headers now quote the corrected source, and the
terminal-pile unit states only its defining equation; finiteness and eventual
stabilization remain Support lemmas.

The integrated tree builds (8,784 jobs, no warnings) and passes all fifteen gates
of `tools/verify.py`, with every registered statement's axiom closure contained
in `{propext, Classical.choice, Quot.sound}`. Integration required only import
repairs and a private rename of a duplicated unit lemma; no statement changed.
