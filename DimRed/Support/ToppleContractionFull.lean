module

public import DimRed.Support.ReflectedThreshold

@[expose] public section

/-!
# Weak topple contraction for signed symmetric piles

A uniform bound on the difference between two times is preserved by the
physical threshold update. Strict integer gaps absorb one firing; at equality,
the directed neighbor bound orders the firing thresholds. Cube-local symmetry
then identifies the cube bound with the maximum on the nonempty simplex.
-/

namespace DimRed.Corrected

open LatticeProb

private theorem odo_representative (d M : ℕ) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d (2 * M) s₀) (t : ℕ) (y : Site d) :
    odo d (2 * M) s₀ t (toSimplexPoint d M y) = odo d (2 * M) s₀ t y := by
  have hsymmetry := (symmetry_lemma d (2 * M) s₀ hsym).1 t
  have hsort := hsymmetry
    (Tuple.sort (fun i => -(foldPoint d (2 * M) y i))) (fun _ => true)
    (foldPoint d (2 * M) y)
  have hrepr : cubeSym d (2 * M)
      (Tuple.sort (fun i => -(foldPoint d (2 * M) y i))) (fun _ => true)
      (foldPoint d (2 * M) y) = toSimplexPoint d M y := by
    funext i
    rfl
  rw [hrepr] at hsort
  rw [hsort, foldPoint]
  exact hsymmetry _ _ y

/-- Time-window increments contract on the nonempty fundamental domain for
every cube-symmetric integer pile, without a restriction on its heights. -/
theorem topple_limit (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s₀ : Site d → ℤ)
    (hsym : Corrected.CubeSymmetric d (2 * M) s₀) (t₀ t j : ℕ) (ht : t₀ ≤ t) :
    Corrected.maximum d M (Corrected.simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t + j) z - odo d (2 * M) s₀ t z) ≤
      Corrected.maximum d M (Corrected.simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z) := by
  have hdnn : 0 ≤ 2 * (d : ℤ) := by
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  let hne := simplexNonempty d M hM
  let C := maximum d M hne
    (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
  have hC : 0 ≤ C := by
    obtain ⟨z, hz⟩ := simplexNonempty d M hM
    have hle := le_maximum d M hne
      (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
      ⟨z, (mem_simplex_iff d M z).1 hz⟩
    have hmono := odo_mono d (2 * M) s₀ (Nat.le_add_right t₀ j) z
    exact le_trans (sub_nonneg.mpr hmono) hle
  have hbase : ∀ y, odo d (2 * M) s₀ (t₀ + j) y - odo d (2 * M) s₀ t₀ y ≤ C := by
    intro y
    by_cases hy : inCube d (2 * M) y
    · have hle := le_maximum d M hne
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z)
        ⟨toSimplexPoint d M y, inSimplex_toSimplexPoint d M y hy⟩
      change odo d (2 * M) s₀ (t₀ + j) (toSimplexPoint d M y) -
        odo d (2 * M) s₀ t₀ (toSimplexPoint d M y) ≤ C at hle
      rwa [odo_representative d M s₀ hsym (t₀ + j) y,
        odo_representative d M s₀ hsym t₀ y] at hle
    · rw [odo_eq_zero_outside d (2 * M) s₀ (t₀ + j) y hy,
        odo_eq_zero_outside d (2 * M) s₀ t₀ y hy, sub_self]
      exact hC
  have hstep : ∀ n y,
      odo d (2 * M) s₀ (t₀ + n + j) y - odo d (2 * M) s₀ (t₀ + n) y ≤ C := by
    intro n
    induction n with
    | zero => simpa only [Nat.add_zero] using hbase
    | succ n ih =>
      intro y
      rw [show t₀ + (n + 1) + j = (t₀ + n + j) + 1 by omega,
        show t₀ + (n + 1) = (t₀ + n) + 1 by omega]
      by_cases hy : inCube d (2 * M) y
      · have hle := ih y
        by_cases hstrict : odo d (2 * M) s₀ (t₀ + n + j) y -
            odo d (2 * M) s₀ (t₀ + n) y < C
        · have ha := (odo_succ_sub_bounds d (2 * M) s₀ (t₀ + n + j) y).2
          have hb := (odo_succ_sub_bounds d (2 * M) s₀ (t₀ + n) y).1
          omega
        · have heq : odo d (2 * M) s₀ (t₀ + n + j) y =
              odo d (2 * M) s₀ (t₀ + n) y + C := by omega
          have hnb := nbrSum_mono (fun z => (sub_le_iff_le_add').1 (ih z)) y
          rw [nbrSum_add_const] at hnb
          have hmul := mul_le_mul_of_nonneg_left (le_of_eq heq.symm) hdnn
          have hsand : sandp d (2 * M) s₀ (t₀ + n + j) y ≤
              sandp d (2 * M) s₀ (t₀ + n) y := by
            dsimp only [sandp, lap]
            nlinarith only [hnb, hmul]
          rw [odo_succ_eq d (2 * M) s₀ (t₀ + n + j) y hy,
            odo_succ_eq d (2 * M) s₀ (t₀ + n) y hy]
          by_cases ha : 2 * (d : ℤ) ≤ sandp d (2 * M) s₀ (t₀ + n + j) y
          · rw [ite_eq_left ha, ite_eq_left (le_trans ha hsand)]
            omega
          · rw [ite_eq_right ha]
            split <;> omega
      · rw [odo_eq_zero_outside d (2 * M) s₀ ((t₀ + n + j) + 1) y hy,
          odo_eq_zero_outside d (2 * M) s₀ ((t₀ + n) + 1) y hy, sub_self]
        exact hC
  apply maximum_le d M hne _ C
  intro z
  have h := hstep (t - t₀) z.val
  rwa [Nat.add_sub_of_le ht] at h

end DimRed.Corrected

namespace ToppleContractionFullAcceptance

open LatticeProb DimRed DimRed.Corrected

-- Both signed and high values occur on the physical cube; exterior values
-- deliberately depend on the coordinate and need not satisfy ambient symmetry.
private def signedPile (y : Site 1) : ℤ :=
  if inCube 1 4 y then (if y 0 = 0 ∨ y 0 = 1 then 4 else -1) else y 0

private theorem signedPile_symmetric : CubeSymmetric 1 4 signedPile := by
  intro π ε y hy
  have hπ : π 0 = 0 := Subsingleton.elim _ _
  have hcube := (cubeSym_inCube 1 4 π ε y).2 hy
  simp only [signedPile, ite_eq_left hy, ite_eq_left hcube]
  have heval : cubeSym 1 4 π ε y 0 = if ε 0 then y 0 else 1 - y 0 := by
    simp only [cubeSym, hπ]
    norm_num [loCoord, hiCoord, sideHalf]
  rw [heval]
  cases hε : ε 0 with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have he : (1 - y 0 = 0 ∨ 1 - y 0 = 1) ↔ (y 0 = 0 ∨ y 0 = 1) := by omega
    simp only [he]
  | true => rfl

-- A nonconstant, signed, high pile has an active first step at its center.
example : signedPile (fun _ => 1) = 4 ∧ signedPile (fun _ => 2) = -1 ∧
    odo 1 4 signedPile 1 (fun _ => 1) = 1 ∧
    odo 1 4 signedPile 1 (fun _ => 2) = 0 := by
  have h1 : inCube 1 4 (fun _ => 1) := by decide
  have h2 : inCube 1 4 (fun _ => 2) := by decide
  norm_num [signedPile, ite_eq_left h1, ite_eq_left h2, odo, lap, DimRed.nbrSum]

example :
    maximum 1 2 (simplexNonempty 1 2 (by decide))
        (fun z => odo 1 4 signedPile (2 + 1) z - odo 1 4 signedPile 2 z) ≤
      maximum 1 2 (simplexNonempty 1 2 (by decide))
        (fun z => odo 1 4 signedPile (0 + 1) z - odo 1 4 signedPile 0 z) := by
  exact topple_limit 1 2 (by decide) (by decide) signedPile signedPile_symmetric
    0 2 1 (by decide)

-- The same example really has no ambient initial symmetry.
example : signedPile
      (cubeSym 1 4 (Equiv.refl (Fin 1)) (fun _ => false) (fun _ => 3)) ≠
    signedPile (fun _ => 3) := by
  norm_num [signedPile, cubeSym, inCube, loCoord, hiCoord, sideHalf, Fin.forall_fin_one]

-- An active nonzero maximum: the center fires and every site fires at most once.
example : maximum 1 2 (simplexNonempty 1 2 (by decide))
    (fun z => odo 1 4 signedPile 1 z - odo 1 4 signedPile 0 z) = 1 := by
  apply le_antisymm
  · apply maximum_le
    intro z
    exact (odo_succ_sub_bounds 1 4 signedPile 0 z.val).2
  · have hz : inSimplex 1 2 (fun _ => 1) := by decide
    have h := le_maximum 1 2 (simplexNonempty 1 2 (by decide))
      (fun z => odo 1 4 signedPile 1 z - odo 1 4 signedPile 0 z) ⟨fun _ => 1, hz⟩
    have hcube : inCube 1 4 (fun _ => 1) := by decide
    have hfire : odo 1 4 signedPile 1 (fun _ => 1) -
        odo 1 4 signedPile 0 (fun _ => 1) = 1 := by
      norm_num [odo, signedPile, ite_eq_left hcube, lap, DimRed.nbrSum]
    change odo 1 4 signedPile 1 (fun _ => 1) - odo 1 4 signedPile 0 (fun _ => 1) ≤ _ at h
    rw [hfire] at h
    exact h

-- A real consumer of both the contraction and independent folded identification.
example (t : ℕ) (x : SimplexSite 1 (sideHalf 4)) :
    foldedOdo 1 4 signedPile (t + 1) x - foldedOdo 1 4 signedPile t x ≤
      maximum 1 2 (simplexNonempty 1 2 (by decide))
        (fun z => odo 1 4 signedPile 1 z - odo 1 4 signedPile 0 z) := by
  have hx : inSimplex 1 2 x.val := x.property
  have hpoint := le_maximum 1 2 (simplexNonempty 1 2 (by decide))
    (fun z => odo 1 4 signedPile (t + 1) z - odo 1 4 signedPile t z) ⟨x.val, hx⟩
  change odo 1 4 signedPile (t + 1) x.val - odo 1 4 signedPile t x.val ≤ _ at hpoint
  rw [(symmetry_lemma 1 4 signedPile signedPile_symmetric).2 (t + 1) x,
    (symmetry_lemma 1 4 signedPile signedPile_symmetric).2 t x] at hpoint
  exact le_trans hpoint
    (topple_limit 1 2 (by decide) (by decide) signedPile signedPile_symmetric
      0 t 1 (Nat.zero_le t))

-- Zero-length windows have actual maximum zero on the same nonempty domain.
example (d M t : ℕ) (hM : 1 ≤ M) (s₀ : Site d → ℤ) :
    maximum d M (simplexNonempty d M hM)
      (fun z => odo d (2 * M) s₀ (t + 0) z - odo d (2 * M) s₀ t z) = 0 := by
  simp only [Nat.add_zero, sub_self, maximum, Finset.sup'_const]

-- The j = 0 instance of the contraction itself, at every horizon and symmetric pile.
example (d M t₀ t : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d (2 * M) s₀) (ht : t₀ ≤ t) :
    maximum d M (simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t + 0) z - odo d (2 * M) s₀ t z) ≤
      maximum d M (simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t₀ + 0) z - odo d (2 * M) s₀ t₀ z) :=
  topple_limit d M hd hM s₀ hsym t₀ t 0 ht

-- The initial-time control is equality, with no extra premise on heights.
example (d M t₀ j : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d (2 * M) s₀) :
    maximum d M (simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z) ≤
      maximum d M (simplexNonempty d M hM)
        (fun z => odo d (2 * M) s₀ (t₀ + j) z - odo d (2 * M) s₀ t₀ z) := by
  exact topple_limit d M hd hM s₀ hsym t₀ t₀ j le_rfl

end ToppleContractionFullAcceptance
