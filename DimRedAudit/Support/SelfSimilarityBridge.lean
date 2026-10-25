module

public import Mathlib
public import DimRed.MainTheorems
public import DimRedAudit.SelfSimilarity.SolutionBasic

@[expose] public section

/-!
# Bridges for `SelfSimilarity`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`DimRedAudit/SelfSimilarity/Challenge.lean`, copied verbatim into
`DimRedAudit/SelfSimilarity/SolutionBasic.lean`, which imports only Mathlib; namespace
`DimRed.StatementAudit`) is a statement-level copy of the repository definitions in
`LatticeProb/Site.lean` (`Site`, `unit`) and `DimRed/Support/Basic.lean` (everything else).
It declares no new types: `Site` is the Mathlib type `Fin d → ℤ` on both sides.  Every
non-recursive definition therefore agrees with its repository counterpart definitionally.
The odometer is defined by structural recursion on time, so its bridge is proved by
induction; the objects built on it follow by rewriting.

This file keeps exactly the bridges that the solution of this pair uses, with those they
depend on: `innerBoundary_eq`, `odo_eq`, `odoUnif_eq`, `toppleTime_eq`.

**It is imported by `DimRedAudit/SelfSimilarity/Solution.lean` only.**  The `Challenge` and
`SolutionBasic` files must stay Mathlib-only: a repository import inside the vocabulary
changes instance elaboration there and breaks the comparator's constant-by-constant closure
check.
-/

namespace DimRed.StatementAudit.Bridge

theorem innerBoundary_eq (d N : ℕ) :
    StatementAudit.innerBoundary d N = DimRed.innerBoundary d N := rfl

/-- The two odometers agree at every time, by induction on the time. -/
theorem odo_eq (d N : ℕ) (s₀ : StatementAudit.Site d → ℤ) (t : ℕ) :
    StatementAudit.odo d N s₀ t = DimRed.odo d N s₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    rw [StatementAudit.odo, DimRed.odo, ih]
    rfl

theorem odoUnif_eq (d N t : ℕ) (x : StatementAudit.Site d) :
    StatementAudit.odoUnif d N t x = DimRed.odoUnif d N t x := by
  rw [StatementAudit.odoUnif, DimRed.odoUnif, odo_eq]

theorem toppleTime_eq (d j : ℕ) :
    StatementAudit.toppleTime d j = DimRed.toppleTime d j := by
  simp only [StatementAudit.toppleTime, DimRed.toppleTime, innerBoundary_eq, odoUnif_eq]

end DimRed.StatementAudit.Bridge
