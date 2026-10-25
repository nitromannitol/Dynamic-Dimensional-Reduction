module

/-
The fundamental domain: every site of the hypercube of side `2M` is carried into
the sorted domain `S_M^{(d)}` by a symmetry of the cube, first folding every
coordinate into `[1, M]` and then sorting the coordinates in decreasing order.
With `simplex_max` and its two bounds this turns a statement about the maximum
over the fundamental domain into a statement about every site.
-/
public import DimRed.Support.Symmetry

@[expose] public section

namespace DimRed

open LatticeProb

theorem loCoord_two_mul (M : ℕ) : loCoord (2 * M) = 1 - (M : ℤ) := by
  simp [loCoord]

theorem hiCoord_two_mul (M : ℕ) : hiCoord (2 * M) = (M : ℤ) := by
  simp [hiCoord, sideHalf]
  omega

/-- The reflection folding every coordinate of `x` into `[1, M]`. -/
def foldPoint (d N : ℕ) (x : Site d) : Site d :=
  cubeSym d N (Equiv.refl (Fin d)) (fun j => decide (1 ≤ x j)) x

/-- The canonical representative of `x` in the sorted fundamental domain. -/
noncomputable def toSimplexPoint (d M : ℕ) (x : Site d) : Site d :=
  fun j => foldPoint d (2 * M) x (Tuple.sort (fun i => -(foldPoint d (2 * M) x i)) j)

theorem foldPoint_apply (d N : ℕ) (x : Site d) (j : Fin d) :
    foldPoint d N x j = if 1 ≤ x j then x j else (loCoord N + hiCoord N) - x j := by
  simp [foldPoint, cubeSym]

theorem odo_toSimplexPoint (d M : ℕ) (s₀ : Site d → ℤ)
    (hsym : IsSymmetricPile d (2 * M) s₀) (t : ℕ) (x : Site d) :
    odo d (2 * M) s₀ t (toSimplexPoint d M x) = odo d (2 * M) s₀ t x := by
  have h1 : odo d (2 * M) s₀ t (toSimplexPoint d M x)
      = odo d (2 * M) s₀ t (foldPoint d (2 * M) x) := by
    have h := odo_cubeSym d (2 * M) s₀ hsym t
      (Tuple.sort (fun i => -(foldPoint d (2 * M) x i))) (fun _ => true)
      (foldPoint d (2 * M) x)
    have e : cubeSym d (2 * M) (Tuple.sort (fun i => -(foldPoint d (2 * M) x i))) (fun _ => true)
        (foldPoint d (2 * M) x) = toSimplexPoint d M x := by
      funext j; simp [cubeSym, toSimplexPoint]
    rwa [e] at h
  rw [h1, foldPoint]
  exact odo_cubeSym d (2 * M) s₀ hsym t _ _ x

theorem foldPoint_mem (d M : ℕ) (x : Site d) (hx : inCube d (2 * M) x) (j : Fin d) :
    1 ≤ foldPoint d (2 * M) x j ∧ foldPoint d (2 * M) x j ≤ (M : ℤ) := by
  have hj := hx j
  rw [loCoord_two_mul, hiCoord_two_mul] at hj
  rw [foldPoint_apply, loCoord_two_mul, hiCoord_two_mul]
  by_cases h1 : 1 ≤ x j
  · rw [if_pos h1]; exact ⟨h1, hj.2⟩
  · rw [if_neg h1]; omega

theorem inSimplex_toSimplexPoint (d M : ℕ) (x : Site d) (hx : inCube d (2 * M) x) :
    inSimplex d M (toSimplexPoint d M x) := by
  constructor
  · intro j
    exact foldPoint_mem d M x hx _
  · intro i j hij
    have hmono := Tuple.monotone_sort (fun i => -(foldPoint d (2 * M) x i)) hij
    simp only [Function.comp_apply] at hmono
    simp only [toSimplexPoint]
    omega

theorem mem_simplex_iff (d M : ℕ) (x : Site d) : x ∈ simplex d M ↔ inSimplex d M x := by
  classical
  simp only [simplex, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun i => (h.1 i).1, fun i => (h.1 i).2⟩, h⟩

theorem le_simplexMax (d M : ℕ) (f : Site d → ℤ) (z : Site d) (hz : inSimplex d M z) :
    f z ≤ simplexMax d M f := by
  have hz' : z ∈ simplex d M := (mem_simplex_iff d M z).2 hz
  have hne : (simplex d M).Nonempty := ⟨z, hz'⟩
  simp only [simplexMax, dif_pos hne]
  exact Finset.le_sup' f hz'

theorem simplexMax_le (d M : ℕ) (f : Site d → ℤ) (c : ℤ) (hc : 0 ≤ c)
    (h : ∀ z, inSimplex d M z → f z ≤ c) : simplexMax d M f ≤ c := by
  by_cases hne : (simplex d M).Nonempty
  · simp only [simplexMax, dif_pos hne]
    exact Finset.sup'_le hne f fun z hz => h z ((mem_simplex_iff d M z).1 hz)
  · simp only [simplexMax, dif_neg hne]; exact hc

theorem nbrSum_add_const {d : ℕ} (f : Site d → ℤ) (c : ℤ) (x : Site d) :
    nbrSum (fun z => f z + c) x = nbrSum f x + 2 * (d : ℤ) * c := by
  simp only [nbrSum]
  rw [show (∑ i : Fin d, (f (x + unit i) + c + (f (x - unit i) + c)))
      = (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) + (∑ _i : Fin d, 2 * c) from by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
  simp [Finset.sum_const, Finset.card_univ]
  ring

theorem simplexMax_nonneg (d M : ℕ) (f : Site d → ℤ) (h : ∀ z, 0 ≤ f z) :
    0 ≤ simplexMax d M f := by
  by_cases hne : (simplex d M).Nonempty
  · obtain ⟨z, hz⟩ := hne
    exact le_trans (h z) (le_simplexMax d M f z ((mem_simplex_iff d M z).1 hz))
  · simp only [simplexMax, dif_neg hne]; exact le_refl 0

end DimRed
