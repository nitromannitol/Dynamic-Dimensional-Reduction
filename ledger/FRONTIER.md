# Frontier — the state of the formalization

Recorded 2026-10-01, when the supervising session changed hands. This file is a record,
not a ruling: it changes nothing about the frozen surface and approves nothing.

## Registered nodes

All 20 nodes of [`manifest.yaml`](manifest.yaml) are `PROVED`: sealed with a clean axiom
closure, and each covered by an independent refute-first audit in [`audits/`](audits/).
`lake build` completes with
no warning and no `sorry`, `lake build DimRedAudit` builds the comparator challenges and their
solutions, and `python3 tools/verify.py` passes all 15 gates. The axiom closure of every
node is exactly `{propext, Classical.choice, Quot.sound}`. The no-hole baseline in
[`holes.json`](holes.json) is `{"holes": {}, "total": 0}`; the `check_progress` gate now
fails if any future change opens a hole in the production tree. An extended independent
refute-first check on 2026-10-01 (`d ≤ 4, M ≤ 8` and `d ≤ 5, M ≤ 6`) found no failure of
any of the ten nodes; see
[`audits/2026-10-01-extended-refutation.md`](audits/2026-10-01-extended-refutation.md).

## Open obligations

None. There is no `DRAFT_SORRY` or `CONDITIONAL` node, no packet in flight, and no `sorry`
under `DimRed/`. The only `sorry`s in the repository are the documented statement-level
placeholders of `DimRedAudit/*/Challenge.lean`, which are not part of the library.

## Items awaiting the owner — do not self-approve

Two records in [`decisions.md`](decisions.md) ask the owner to confirm a reading. Both
concern the wording of an already-approved paper repair; neither changes a frozen statement.

1. `prop-base-dimension-strong-derivative`: the paper leaves the bold `x` of the display
   unbound, and the frozen statement reads it as the facet point `(x_i, 1, 1_j)`. The
   broader reading over all of `S_M` is refuted, so the facet-point reading is the only
   true one; the owner should confirm it. The evidence is in the "reading of the strong
   derivative clause" section of `decisions.md` and in
   [`audits/2026-09-30-seal-audit.md`](audits/2026-09-30-seal-audit.md) §3.

2. `paper/CHANGES_FROM_ARXIV.md`, last section: the erratum's attribution was corrected
   on 2026-10-01 to name `DimRed.facet_step_of_earlier`
   (`DimRed/Support/FacetStepFinal.lean`) for the strong-facet clause and
   `DimRed.odo_jump_of_gap` for the gap step, so it no longer names
   `DimRed.strong_facet_step_of_reg` for the clause; that lemma supplies only the
   "stays put" half. What remains for the owner is the paper's proof narrative itself
   (whether the comparison is used, and under what hypothesis), as recorded in
   `decisions.md`.

A third reading is settled by design and is not an obligation: `lem-symmetry` states only
the first sentence of Lemma 2.3. The second sentence (`v_t = v_t^S` on `S_M`) is the
definitional reading of the development, which defines no separate symmetrized odometer; it
is documented in [`../CORRESPONDENCE.md`](../CORRESPONDENCE.md) and adding it as a frozen
clause would need the owner's approval.
