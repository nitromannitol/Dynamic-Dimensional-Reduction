"""Check that every theorem-like statement in the paper is formalized.

The manifest says which paper statement each Lean node transcribes.  This asks
the complementary question, which no other checker asks: is there a statement in
the paper that no node claims?  A formalization can be entirely axiom-clean and
still be silently incomplete, so the gap is worth a gate of its own.

Open problems (the `problem` environment of Section 9) are excluded: they are
questions, not claims.

    python3 tools/check_coverage.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_coverage.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
def _paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$DIMRED_PAPER`."""
    env = os.environ.get("DIMRED_PAPER")
    return Path(env) if env else ROOT / "paper" / "dimred.tex"


PAPER = _paper_path()

STATEMENT_ENVS = ("theorem", "lemma", "proposition", "prop", "corollary")
LABEL_IN_STATEMENT = re.compile(
    r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}(?:\[[^\]]*\])?[^\\]*\\label\{([^}]+)\}")
# A node names the paper statement it transcribes as `(label <name>)`.  The
# paper's own labels are bare words (`the_theorem`), so a prefix cannot be
# required; the word `label` is what marks the name.
LABEL_TOKEN = re.compile(r"label\s+([A-Za-z][A-Za-z0-9:_-]*)")
# A statement the paper leaves unlabelled cannot be claimed by name, so a node
# claims it by line: the `source:` range must contain the line it opens on.
BEGIN_STATEMENT = re.compile(r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}")
SOURCE_RANGE = re.compile(re.escape(PAPER.name) + r":(\d+)-(\d+)")


def label_variants(label: str) -> list[str]:
    """A source may write `cor-derivative_bound` for `\\label{cor:derivative_bound}`."""
    out = [label]
    if "-" in label and ":" not in label:
        out.append(label.replace("-", ":", 1))
    return out


def main() -> int:
    if not PAPER.exists():
        print(f"check_coverage: paper not found at {PAPER}", file=sys.stderr)
        return 2
    text = PAPER.read_text(encoding="utf-8")
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    claimed: set[str] = set()
    ranges: list[tuple[int, int]] = []
    for node in manifest.get("nodes") or []:
        for label in LABEL_TOKEN.findall(node["source"]):
            claimed.update(label_variants(label))
        span = SOURCE_RANGE.search(node["source"])
        if span:
            ranges.append((int(span.group(1)), int(span.group(2))))

    statements = []
    seen = set()
    for m in LABEL_IN_STATEMENT.finditer(text):
        if m.group(2) not in seen:
            seen.add(m.group(2))
            statements.append((m.group(1), m.group(2), text[:m.start()].count("\n") + 1))

    uncovered = [(k, lab, ln) for k, lab, ln in statements if lab not in claimed]

    # Unlabelled statements, claimed by line rather than by name.
    labelled_lines = {ln for _, _, ln in statements}
    for m in BEGIN_STATEMENT.finditer(text):
        ln = text[:m.start()].count("\n") + 1
        if ln in labelled_lines:
            continue
        statements.append((m.group(1), f"(unlabelled, line {ln})", ln))
        if not any(a <= ln <= b for a, b in ranges):
            uncovered.append((m.group(1), f"(unlabelled, line {ln})", ln))

    statements.sort(key=lambda s: s[2])
    uncovered.sort(key=lambda s: s[2])

    print(f"check_coverage: {len(statements)} statements in the paper, "
          f"{len(statements) - len(uncovered)} formalized")
    if uncovered:
        print("\nNot claimed by any manifest node:")
        for kind, lab, ln in uncovered:
            print(f"  dimred.tex:{ln}  {kind} {lab}")
        print("\ncheck_coverage: the formalization does not cover the whole paper",
              file=sys.stderr)
        return 1
    print("every theorem, lemma and proposition in the paper is formalized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
