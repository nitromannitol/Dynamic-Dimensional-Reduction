#!/usr/bin/env python3
"""Run this repository's deterministic gates.

    python3 tools/verify.py              # the whole pipeline
    python3 tools/verify.py --skip-lake  # the pure-Python gates only

The gates themselves are not in this repository. They live in
`tools/leanform/`, a vendored copy of the shared checker package, and the
gates run from it.

Paper-specific data comes from `ledger/manifest.yaml` and
`ledger/readings.yaml`, never from a literal in a checker: a checker whose
regex named a different paper passed while inspecting nothing.
"""

import pathlib
import sys

_HERE = pathlib.Path(__file__).resolve().parent
_PKG = _HERE / "leanform"

if not (_PKG / "leanform_tools").is_dir():
    sys.exit(f"{_PKG}/leanform_tools is missing.")

sys.path.insert(0, str(_PKG))

from leanform_tools import verify  # noqa: E402

if __name__ == "__main__":
    argv = list(sys.argv)
    # Default to this repository rather than the current directory, so the
    # command works from anywhere in the tree.
    if len(argv) == 1 or argv[1].startswith("-"):
        argv.insert(1, str(_HERE.parent))
    sys.exit(verify.main(argv))
