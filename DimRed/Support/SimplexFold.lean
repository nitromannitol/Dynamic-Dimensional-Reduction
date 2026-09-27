/-
The odometer is invariant under the canonical folding of a point of the
hypercube into the sorted fundamental domain, in the form needed by the
dimensional-reduction step: the reduction identity is stated for points of the
sorted domain, and a raw point of the cube is carried there by
`toSimplexPoint` without changing the odometer.

`toSimplexPoint` is `cubeSym` applied to the reflection folding every coordinate
into `[1, M]` followed by the sorting permutation, so the invariance is the
symmetry lemma `odo_cubeSym` at the symmetry `snocPerm`/`snocEps` of the
appended coordinate.
-/
import DimRed.Support.Fundamental
import DimRed.Support.SandpileFromOdo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The folding of a point of the hypercube into the sorted domain is the
symmetry `cubeSym` at the sorting permutation of the folded coordinates. -/
theorem toSimplexPoint_eq_cubeSym (d M : ℕ) (z : Site d) :
    toSimplexPoint d M z
      = cubeSym d (2 * M) (Tuple.sort (fun j => -(foldPoint d (2 * M) z j)))
          (fun _ => true) (foldPoint d (2 * M) z) := by
  funext j
  rw [toSimplexPoint]
  rfl

/-- The odometer is unchanged by the folding into the sorted domain. -/
theorem odoUnif_toSimplexPoint (d M t : ℕ) (z : Site d) :
    odoUnif d (2 * M) t (toSimplexPoint d M z) = odoUnif d (2 * M) t z := by
  simpa [odoUnif] using odo_toSimplexPoint d M (fun _ => 2 * (d : ℤ))
    (isSymmetricPile_const' d (2 * M) (2 * (d : ℤ))) t z

/-- Appending a coordinate to the folded point does not change the odometer in
one higher dimension. -/
theorem odoUnif_snoc_toSimplexPoint (d M t : ℕ) (z : Site d) :
    odoUnif (d + 1) (2 * M) t (Fin.snoc (toSimplexPoint d M z) 1)
      = odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) := by
  have h := odo_cubeSym (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
    (isSymmetricPile_const' (d + 1) (2 * M) (2 * ((d + 1 : ℕ) : ℤ))) t
    (snocPerm (Tuple.sort (fun j => -(foldPoint d (2 * M) z j))))
    (snocEps (fun _ => true)) (Fin.snoc (foldPoint d (2 * M) z) 1)
  rw [cubeSym_snoc] at h
  have he : cubeSym d (2 * M) (Tuple.sort (fun j => -(foldPoint d (2 * M) z j)))
      (fun _ => true) (foldPoint d (2 * M) z) = toSimplexPoint d M z :=
    (toSimplexPoint_eq_cubeSym d M z).symm
  rw [he] at h
  have hfold : odoUnif (d + 1) (2 * M) t (Fin.snoc (foldPoint d (2 * M) z) 1)
      = odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) := by
    have h2 := odo_cubeSym (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
      (isSymmetricPile_const' (d + 1) (2 * M) (2 * ((d + 1 : ℕ) : ℤ))) t
      (snocPerm (Equiv.refl (Fin d))) (snocEps (fun j => decide (1 ≤ z j)))
      (Fin.snoc z 1)
    rw [cubeSym_snoc] at h2
    have he2 : cubeSym d (2 * M) (Equiv.refl (Fin d)) (fun j => decide (1 ≤ z j)) z
        = foldPoint d (2 * M) z := rfl
    rw [he2] at h2
    simpa [odoUnif] using h2
  rw [← hfold]
  simpa [odoUnif] using h

end DimRed
