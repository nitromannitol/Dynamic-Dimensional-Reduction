"""Check that every theorem-like statement in the paper is claimed.

The manifest says which paper statement each Lean node transcribes. This asks
the complementary question, which no other checker asks: is there a statement
in the paper that no node claims? A formalization can be entirely axiom-clean
and still be silently incomplete, so the gap is worth a gate of its own.

`problem` and open-problem environments are excluded: they are questions, not
claims. They are excluded simply by never appearing in `STATEMENT_ENVS`.

    python3 -m leanform_tools.check_coverage <repo>

The statement environments are the union of the spellings used by the surveyed
papers, and each rule below is enforced:

* The paper path, its basename and the claim regex all come from `cfg`.
* `STATEMENT_ENVS` includes `definition` and `prop`. A paper may define its
  proposition environment as `\\prop` rather than `\\proposition`; if the checker
  knew only one spelling, every `\\begin{prop}` statement would be invisible
  while the check still exited 0.
* An unlabeled statement environment is a hard error, reported distinctly from an
  uncovered one. A checker that needs a `\\label` to recognize an environment
  silently skips an unlabeled statement, so this rule reports it instead.
* A node's claim on a label is recognized by substring search over the node's
  whole `source:` text (canonicalized for the hyphen/colon ambiguity
  `paper_anchors.label_variants` already handles), not by requiring a
  `label <lab>` keyword or a `thm:`/`lem:`-style prefix. This lets a claim that
  carries no paper line citation, or a label outside any common prefix family,
  still count.
"""

from __future__ import annotations

import re
import sys

from .config import ConfigError, RepoConfig, load
from .gate import Result, run
from .paper_anchors import label_variants

# `problem`/`openproblem`/`open-problem` are deliberately absent: they are
# questions, not claims, and are excluded simply by omission here.
STATEMENT_ENVS = ("theorem", "lemma", "proposition", "prop", "corollary",
                   "definition")

_STATEMENT_RE = re.compile(
    r"\\begin\{(" + "|".join(re.escape(e) for e in STATEMENT_ENVS) + r")\}"
    r"(.*?)\\end\{\1\}",
    re.DOTALL,
)
_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def _strip_comments(text: str) -> str:
    """Drop `%...` comments while preserving line numbers."""
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def check(res: Result, cfg: RepoConfig) -> None:
    if not cfg.paper_path.exists():
        raise ConfigError(f"paper not found at {cfg.paper_path}")
    text = _strip_comments(cfg.paper_path.read_text(encoding="utf-8"))

    # The corpus a claim is searched in: every node's whole `source:` text,
    # not just the primary label slot, so a prose mention ("discharged by
    # <label>") counts as a claim.
    claimed_blob = "\n".join(n.source for n in cfg.nodes if n.source)

    statements: list[tuple[str, str, int]] = []
    unlabeled: list[tuple[str, int]] = []
    seen: set[str] = set()
    for m in _STATEMENT_RE.finditer(text):
        kind, body = m.group(1), m.group(2)
        line = text[:m.start()].count("\n") + 1
        lm = _LABEL_RE.search(body)
        if lm is None:
            unlabeled.append((kind, line))
            continue
        label = lm.group(1)
        if label in seen:
            continue
        seen.add(label)
        statements.append((kind, label, line))

    res.total = len(statements) + len(unlabeled)

    uncovered = []
    for kind, label, line in statements:
        res.count()
        variants = label_variants(label)
        if not any(re.search(rf"\b{re.escape(v)}\b", claimed_blob) for v in variants):
            uncovered.append((kind, label, line))

    for kind, line in unlabeled:
        res.count()
        res.fail(f"{cfg.paper_stem}:{line}: UNLABELED {kind} environment -- "
                 "fix the paper, not the checker")

    for kind, label, line in uncovered:
        res.fail(f"{cfg.paper_stem}:{line}: {kind} {label} is not claimed by "
                 "any manifest node")

    represented = len(statements) - len(uncovered)
    res.note(f"{len(statements) + len(unlabeled)} statements in the paper, "
              f"{represented} represented")
    if unlabeled:
        res.note(f"{len(unlabeled)} unlabeled statement environment(s) -- "
                  "these cannot be claimed by any node until labeled")


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_coverage", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
