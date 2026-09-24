# Contributing / Building notes

This repository is a formalization in progress: 10 of its 20 registered statements are
proved, and the other 10, including every main result of the paper, are open.  Issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings other than one
`declaration uses 'sorry'` warning for each open registered statement
(`python3 tools/check_warnings.py`).  A `sorry` anywhere else, or a second one in an open
node's file, fails `python3 tools/check_manifest.py`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/DimRed` (and the
  corresponding `.lake/build/ir/DimRed`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `DimRed/Frozen/` is pinned by the SHA-256
  recorded in `ledger/manifest.yaml`.  A change there shows up in
  `python3 tools/check_manifest.py` and must be recorded in the manifest;
  proofs after the end marker may be changed freely.

- **Closing an open node.**  Replace the node's `sorry` by a proof, confirm with
  `python3 tools/check_axioms.py` that its axiom closure no longer contains `sorryAx`,
  set its `state` to `SEALED` in the manifest, and regenerate the documentation with
  `python3 tools/sync_docs.py --write`.  When a main theorem is sealed, restate it in
  `DimRed/MainTheorems.lean`, add it to `DimRed/Meta/AxiomsAudit.lean`, and add its
  comparator challenge under `Audit/`.

- **Library lemmas.**  Lattice objects that do not depend on this paper belong in the
  shared library Lattice-Probability.

- **The proved results** are in `DimRed/MainTheorems.lean`; the axiom audit is
  `lake build DimRed.Meta.AxiomsAudit`.  `python3 tools/verify.py` runs every checker.
