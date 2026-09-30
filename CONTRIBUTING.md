# Contributing / Building notes

All 20 registered statements of this repository are proved, the paper's main results
included.  Issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings (the `check_warnings`
gate); a registered statement reopened as a draft may carry one `declaration uses 'sorry'`
warning, and a `sorry` anywhere else fails the `check_manifest` gate.  Run `python3 tools/verify.py` from the repository root for every
gate, or `cd tools/leanform && python3 -m leanform_tools.<gate> ../..` for one.

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
  the `check_manifest` gate and must be recorded in the manifest;
  proofs after the end marker may be changed freely.

- **Closing an open node.**  Replace the node's `sorry` by a proof, confirm with
  the `check_axioms` gate that its axiom closure no longer contains `sorryAx`,
  set its `state` to `SEALED` in the manifest, and regenerate the documentation
  with `cd tools/leanform && python3 -m leanform_tools.sync_docs ../.. --write`.
  When a main theorem is sealed, restate it in `DimRed/MainTheorems.lean`, add it
  to `DimRed/Meta/AxiomsAudit.lean`, and add its comparator challenge under
  `Audit/`.

- **Library lemmas.**  Lattice objects that do not depend on this paper belong in the
  shared library Lattice-Probability.

- **The proved results** are in `DimRed/MainTheorems.lean`; the axiom audit is
  `lake build DimRed.Meta.AxiomsAudit`.  `python3 tools/verify.py` runs every checker.
