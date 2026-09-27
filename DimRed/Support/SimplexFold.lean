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
import DimRed.Support.StrongDerivPure
import DimRed.Support.FacetNormal

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

/-- A point of `ℤ^i` outside the hypercube has its extension by a trailing one
outside the hypercube of one higher dimension. -/
theorem not_inCube_snoc_one {i M : ℕ} {z : Site i} (hz : ¬ inCube i (2 * M) z) :
    ¬ inCube (i + 1) (2 * M) (Fin.snoc z 1) := by
  intro hc
  apply hz
  intro l
  have h := hc l.castSucc
  rwa [Fin.snoc_castSucc] at h

/-- The reduction identity at scale `M` for an arbitrary point of `ℤ^i`, from the
identity on the sorted domain. -/
theorem odoUnif_snoc_of_reduction (i M q : ℕ)
    (hred : ∀ w : Site i, inSimplex i M w →
      odoUnif (i + 1) (2 * M) q (Fin.snoc w 1) = odoUnif i (2 * M) q w) :
    ∀ z : Site i,
      odoUnif (i + 1) (2 * M) q (Fin.snoc z 1) = odoUnif i (2 * M) q z := by
  intro z
  by_cases hz : inCube i (2 * M) z
  · have h := hred (toSimplexPoint i M z) (inSimplex_toSimplexPoint i M z hz)
    rw [odoUnif_snoc_toSimplexPoint i M q z, odoUnif_toSimplexPoint i M q z] at h
    exact h
  · have h1 : odoUnif i (2 * M) q z = 0 :=
      odo_eq_zero_outside i (2 * M) (fun _ => 2 * (i : ℤ)) q z hz
    have h2 : odoUnif (i + 1) (2 * M) q (Fin.snoc z 1) = 0 :=
      odo_eq_zero_outside (i + 1) (2 * M) (fun _ => 2 * ((i + 1 : ℕ) : ℤ)) q _
        (not_inCube_snoc_one hz)
    rw [h1, h2]

/-- At a point of the sorted domain all of whose coordinates exceed one, the
facet normal form of its extension by a trailing one has a nonempty head: the
head is the number of coordinates at least two, which is all of them. -/
theorem facet_normal_form_snoc_one (e M : ℕ) (he1 : 1 ≤ e) (z : Site e)
    (hz : inSimplex e M z) (hz1 : ∀ k, 1 < z k) :
    ∃ (i j : ℕ) (_ : i + 1 + j = e + 1) (w : Fin i → ℤ), (∀ a, 2 ≤ w a) ∧
      inSimplex (i + 1 + j) M (facetPoint w 1 j) ∧ (1 ≤ i) ∧
      ∀ t, odoUnif (e + 1) (2 * M) t (Fin.snoc z 1)
          = odoUnif (i + 1 + j) (2 * M) t (facetPoint w 1 j) ∧
        odoUnif (e + 1) (2 * M) t (Fin.snoc z 1 + unit (Fin.last e))
          = odoUnif (i + 1 + j) (2 * M) t (facetPoint w 2 j) := by
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    have h := (hz.1 ⟨e - 1, by omega⟩).2
    have h2 := hz1 ⟨e - 1, by omega⟩
    omega
  have hpos : inPos (e + 1) M (Fin.snoc z 1) := by
    intro l
    refine Fin.lastCases ?_ (fun a => ?_) l
    · rw [Fin.snoc_last]
      exact ⟨by norm_num, hM1⟩
    · rw [Fin.snoc_castSucc]
      exact hz.1 a
  have hk : (Fin.snoc z 1 : Site (e + 1)) (Fin.last e) = 1 := by rw [Fin.snoc_last]
  obtain ⟨i, j, hij, w, hw2, hws, hi, hodo⟩ :=
    facet_normal_form (e + 1) M (Fin.snoc z 1) hpos (Fin.last e) hk
  refine ⟨i, j, hij, w, hw2, hws, ?_, hodo⟩
  exact hi ⟨Fin.castSucc ⟨e - 1, by omega⟩, by
    rw [Fin.snoc_castSucc]
    have h := hz1 ⟨e - 1, by omega⟩
    omega⟩

end DimRed
