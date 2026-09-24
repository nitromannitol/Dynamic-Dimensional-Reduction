#!/usr/bin/env python3
"""Run every verification check of this work-in-progress formalization.

Every checker must pass, with one exception by design: `check_axioms.py` fails
while any registered statement is open, because the axiom closure of an open
node contains `sorryAx`.  Its report is therefore compared with the manifest
instead: a `SEALED` node must be clean, and every node whose closure contains
`sorryAx` must be recorded as `DRAFT_SORRY` or `CONDITIONAL`.  A sealed node
that loses its proof, or an open node recorded as sealed, fails here.
"""
import os
from pathlib import Path
import re
import subprocess
import sys

try:
    import yaml
except ImportError:
    sys.exit("verify.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
CHECKS = ("check_manifest", "check_coverage", "check_clauses", "check_constants",
          "check_exponents", "paper_anchors", "paper_citations", "sync_docs",
          "assumptions", "check_warnings")


def axiom_closures(env) -> int:
    """Compare the axiom closure of every node with its recorded state."""
    cmd = [sys.executable, "tools/check_axioms.py"]
    print("\n" + " ".join(cmd), flush=True)
    run = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    sys.stdout.write(run.stdout)
    clean = set(re.findall(r"^\s+clean\s+(\S+)", run.stdout, re.M))
    dirty = set(re.findall(r"^\s+sorryAx\s+(\S+)", run.stdout, re.M))
    missing = set(re.findall(r"^\s+\?\?\s+(\S+)", run.stdout, re.M))
    nodes = yaml.safe_load((ROOT / "ledger/manifest.yaml").read_text(encoding="utf-8"))["nodes"]
    state = {n["id"]: n["state"] for n in nodes}
    bad = sorted(missing)
    bad += [i for i in sorted(dirty) if state[i] not in ("DRAFT_SORRY", "CONDITIONAL")]
    bad += [i for i, s in state.items() if s == "SEALED" and i not in clean]
    if bad or len(clean | dirty) != len(state):
        print(f"verify: axiom closures disagree with the manifest: {bad}")
        return 1
    print(f"verify: axiom closures agree with the manifest ({len(clean)} clean, "
          f"{len(dirty)} open or resting on open nodes)")
    return 0


def main():
    env = {**os.environ, "PATH": str(Path.home() / ".elan/bin") + ":" + os.environ.get("PATH", "")}
    for name in CHECKS:
        cmd = [sys.executable, f"tools/{name}.py"] + (["--check"] if name == "assumptions" else [])
        print("\n" + " ".join(cmd), flush=True)
        result = subprocess.run(cmd, cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
    if axiom_closures(env):
        return 1
    print("\nverify: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
