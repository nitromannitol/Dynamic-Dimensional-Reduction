import Mathlib
import DimRed.MainTheorems
import Audit.Support.Vocabulary

/-!
# Bridges from the Mathlib-only vocabulary to the repository

The challenge vocabulary (`Audit/Support/Vocabulary.lean`, namespace
`DimRed.StatementAudit`) is a statement-level copy of the repository definitions in
`LatticeProb/Site.lean` (`Site`, `unit`) and `DimRed/Support/Basic.lean` (everything else).
It declares no new types: `Site` is the Mathlib type `Fin d → ℤ` on both sides.  Every
non-recursive definition therefore agrees with its repository counterpart definitionally.
The odometer is defined by structural recursion on time, so its bridge is proved by
induction; the objects built on it follow by rewriting.
-/

namespace DimRed.StatementAudit.Bridge

theorem sideHalf_eq (N : ℕ) : StatementAudit.sideHalf N = DimRed.sideHalf N := rfl

theorem inSimplex_iff (d M : ℕ) (x : StatementAudit.Site d) :
    StatementAudit.inSimplex d M x ↔ DimRed.inSimplex d M x := Iff.rfl

theorem innerBoundary_eq (d N : ℕ) :
    StatementAudit.innerBoundary d N = DimRed.innerBoundary d N := rfl

theorem lap_eq {d : ℕ} (u : StatementAudit.Site d → ℤ) (x : StatementAudit.Site d) :
    StatementAudit.lap u x = DimRed.lap u x := rfl

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

theorem sandpUnif_eq (d N t : ℕ) (x : StatementAudit.Site d) :
    StatementAudit.sandpUnif d N t x = DimRed.sandpUnif d N t x := by
  rw [StatementAudit.sandpUnif, StatementAudit.sandp, DimRed.sandpUnif, DimRed.sandp,
    odo_eq, lap_eq]

theorem odoInfUnif_eq (d N : ℕ) (x : StatementAudit.Site d) :
    StatementAudit.odoInfUnif d N x = DimRed.odoInfUnif d N x := by
  simp only [StatementAudit.odoInfUnif, StatementAudit.odoInf, DimRed.odoInfUnif,
    DimRed.odoInf, odo_eq]

theorem sandpInfUnif_eq (d N : ℕ) (x : StatementAudit.Site d) :
    StatementAudit.sandpInfUnif d N x = DimRed.sandpInfUnif d N x := by
  simp only [StatementAudit.sandpInfUnif, DimRed.sandpInfUnif, odoInfUnif_eq, lap_eq]

theorem toppleTime_eq (d j : ℕ) :
    StatementAudit.toppleTime d j = DimRed.toppleTime d j := by
  simp only [StatementAudit.toppleTime, DimRed.toppleTime, innerBoundary_eq, odoUnif_eq]

theorem simplex_eq (d M : ℕ) : StatementAudit.simplex d M = DimRed.simplex d M := by
  ext x
  simp only [StatementAudit.simplex, DimRed.simplex, Finset.mem_filter, Finset.mem_Icc,
    StatementAudit.inSimplex, DimRed.inSimplex]

theorem simplexMax_eq (d M : ℕ) (f : StatementAudit.Site d → ℤ) :
    StatementAudit.simplexMax d M f = DimRed.simplexMax d M f := by
  simp only [StatementAudit.simplexMax, DimRed.simplexMax, simplex_eq]

theorem facetPoint_eq {i : ℕ} (x : Fin i → ℤ) (c : ℤ) (j : ℕ) :
    StatementAudit.facetPoint x c j = DimRed.facetPoint x c j := rfl

end DimRed.StatementAudit.Bridge
