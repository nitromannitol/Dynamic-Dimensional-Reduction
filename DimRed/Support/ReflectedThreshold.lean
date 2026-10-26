module

public import DimRed.Support.Radial
public import DimRed.Support.SourceCarriers
public import DimRed.Support.SandpileFromOdo

@[expose] public section

/-!
# The independent folded threshold process

Each directed physical neighbor contributes its representative's value when it
lies in the cube and zero otherwise. The two signs and every coordinate are
counted separately, including coincident representatives. The recurrence uses
the physical firing threshold, with no restriction on the initial integer pile.
-/

namespace DimRed.Corrected

open LatticeProb

/-- Lift a function on the fundamental domain to the cube, with zero exterior. -/
noncomputable def foldedLift (d N : ℕ)
    (v : SimplexSite d (sideHalf N) → ℤ) (y : Site d) : ℤ :=
  if hy : inCube d N y then
    v ⟨toSimplexPointN d N y, inSimplex_toSimplexPointN d N y hy⟩
  else 0

/-- Sum over all directed neighbor occurrences; representatives are not deduplicated. -/
noncomputable def foldedNbrSum (d N : ℕ)
    (v : SimplexSite d (sideHalf N) → ℤ) (x : SimplexSite d (sideHalf N)) : ℤ :=
  ∑ i : Fin d,
    (foldedLift d N v (x.val + unit i) + foldedLift d N v (x.val - unit i))

/-- Independent parallel threshold evolution on the fundamental domain. -/
noncomputable def foldedOdo (d N : ℕ) (s₀ : Site d → ℤ) :
    ℕ → SimplexSite d (sideHalf N) → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      foldedOdo d N s₀ t x +
        (if 2 * (d : ℤ) ≤ s₀ x.val + foldedNbrSum d N (foldedOdo d N s₀ t) x -
          2 * (d : ℤ) * foldedOdo d N s₀ t x then 1 else 0)

theorem foldedLift_of_inCube (d N : ℕ)
    (v : SimplexSite d (sideHalf N) → ℤ) (y : Site d) (hy : inCube d N y) :
    foldedLift d N v y =
      v ⟨toSimplexPointN d N y, inSimplex_toSimplexPointN d N y hy⟩ := by
  rw [foldedLift, dite_eq_left hy]

theorem foldedLift_of_not_inCube (d N : ℕ)
    (v : SimplexSite d (sideHalf N) → ℤ) (y : Site d) (hy : ¬ inCube d N y) :
    foldedLift d N v y = 0 := by
  rw [foldedLift, dite_eq_right hy]

theorem foldedNbrSum_eq_nbrSum (d N : ℕ)
    (v : SimplexSite d (sideHalf N) → ℤ) (x : SimplexSite d (sideHalf N)) :
    foldedNbrSum d N v x = nbrSum (foldedLift d N v) x.val := rfl

@[simp] theorem foldedLift_zero (d N : ℕ) (y : Site d) :
    foldedLift d N (fun _ => 0) y = 0 := by
  unfold foldedLift
  split <;> rfl

@[simp] theorem foldedOdo_zero (d N : ℕ) (s₀ : Site d → ℤ)
    (x : SimplexSite d (sideHalf N)) : foldedOdo d N s₀ 0 x = 0 := rfl

theorem foldedOdo_succ (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ)
    (x : SimplexSite d (sideHalf N)) :
    foldedOdo d N s₀ (t + 1) x = foldedOdo d N s₀ t x +
      (if 2 * (d : ℤ) ≤ s₀ x.val + foldedNbrSum d N (foldedOdo d N s₀ t) x -
        2 * (d : ℤ) * foldedOdo d N s₀ t x then 1 else 0) := rfl

/-- At the first step, every signed or high initial value uses a single indicator. -/
theorem foldedOdo_one (d N : ℕ) (s₀ : Site d → ℤ)
    (x : SimplexSite d (sideHalf N)) :
    foldedOdo d N s₀ 1 x = if 2 * (d : ℤ) ≤ s₀ x.val then 1 else 0 := by
  simp only [foldedOdo, foldedNbrSum, foldedLift_zero, add_zero, Finset.sum_const_zero,
    mul_zero, sub_zero, zero_add]

private theorem odo_congr_on_cube (d N : ℕ) (s₀ s₁ : Site d → ℤ)
    (h : ∀ x, inCube d N x → s₀ x = s₁ x) (t : ℕ) :
    odo d N s₀ t = odo d N s₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    by_cases hx : inCube d N x
    · simp only [odo, ite_eq_left hx, ih, h x hx]
    · simp only [odo, ite_eq_right hx]

/-- Cube-local initial symmetry suffices for ambient odometer symmetry. -/
theorem odo_cubeSym_of_cubeSymmetric (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d N s₀) (t : ℕ)
    (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) :
    odo d N s₀ t (cubeSym d N π ε x) = odo d N s₀ t x := by
  let s₁ : Site d → ℤ := fun y => if inCube d N y then s₀ y else 0
  have hsym₁ : IsSymmetricPile d N s₁ := by
    intro ρ δ y
    dsimp only [s₁]
    simp only [cubeSym_inCube]
    by_cases hy : inCube d N y
    · simp only [ite_eq_left hy, hsym ρ δ y hy]
    · simp only [ite_eq_right hy]
  have heq : odo d N s₀ t = odo d N s₁ t :=
    odo_congr_on_cube d N s₀ s₁ (fun y hy => by simp only [s₁, ite_eq_left hy]) t
  rw [heq]
  exact odo_cubeSym d N s₁ hsym₁ t π ε x

private theorem odo_toSimplexPointN (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d N s₀) (t : ℕ) (y : Site d) :
    odo d N s₀ t (toSimplexPointN d N y) = odo d N s₀ t y := by
  rw [← cubeSym_toSimplexPointN]
  rw [odo_cubeSym_of_cubeSymmetric d N s₀ hsym t]
  unfold foldPointN
  exact odo_cubeSym_of_cubeSymmetric d N s₀ hsym t _ _ y

private theorem simplex_in_cube (d N : ℕ) (x : SimplexSite d (sideHalf N)) :
    inCube d N x.val := by
  intro i
  have hi := x.property.1 i
  simp only [loCoord, hiCoord]
  exact ⟨by omega, hi.2⟩

/-- The independently defined folded evolution equals the physical odometer. -/
theorem odo_eq_foldedOdo (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d N s₀) (t : ℕ) (x : SimplexSite d (sideHalf N)) :
    odo d N s₀ t x.val = foldedOdo d N s₀ t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hlift : foldedLift d N (foldedOdo d N s₀ t) = odo d N s₀ t := by
      funext y
      by_cases hy : inCube d N y
      · rw [foldedLift_of_inCube d N _ y hy, ← ih]
        exact odo_toSimplexPointN d N s₀ hsym t y
      · rw [foldedLift_of_not_inCube d N _ y hy,
          odo_eq_zero_outside d N s₀ t y hy]
    rw [odo_succ_eq d N s₀ t x.val (simplex_in_cube d N x), foldedOdo_succ]
    rw [foldedNbrSum_eq_nbrSum, hlift]
    simp only [sandp, lap, ih]
    congr 2
    congr 1
    ring

/-- The folded trajectory lifts to the physical odometer, including its zero exterior. -/
theorem foldedLift_foldedOdo (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : CubeSymmetric d N s₀) (t : ℕ) (y : Site d) :
    foldedLift d N (foldedOdo d N s₀ t) y = odo d N s₀ t y := by
  by_cases hy : inCube d N y
  · rw [foldedLift_of_inCube d N _ y hy, ← odo_eq_foldedOdo d N s₀ hsym t]
    exact odo_toSimplexPointN d N s₀ hsym t y
  · rw [foldedLift_of_not_inCube d N _ y hy, odo_eq_zero_outside d N s₀ t y hy]

/-- Physical symmetry and identification with the independent folded process. -/
theorem symmetry_lemma (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : Corrected.CubeSymmetric d N s₀) :
    (∀ (t : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d),
      odo d N s₀ t (cubeSym d N π ε x) = odo d N s₀ t x) ∧
    (∀ (t : ℕ) (x : Corrected.SimplexSite d (sideHalf N)),
      odo d N s₀ t x.val = Corrected.foldedOdo d N s₀ t x) :=
  ⟨odo_cubeSym_of_cubeSymmetric d N s₀ hsym, odo_eq_foldedOdo d N s₀ hsym⟩

end DimRed.Corrected


namespace ReflectedThresholdAcceptance
open LatticeProb DimRed DimRed.Corrected

-- The signed/high first steps use the exact identification conclusion.
example (c : ℤ) (x : SimplexSite 1 (sideHalf 4)) :
    odo 1 4 (fun _ => c) 1 x.val = foldedOdo 1 4 (fun _ => c) 1 x ∧
    foldedOdo 1 4 (fun _ => c) 1 x = if 2 ≤ c then 1 else 0 := by
  exact ⟨(symmetry_lemma 1 4 (fun _ => c) (fun _ _ _ _ => rfl)).2 1 x,
    by simpa only [Nat.cast_one, mul_one] using foldedOdo_one 1 4 (fun _ => c) x⟩

example (x : SimplexSite 1 (sideHalf 4)) :
    odo 1 4 (fun _ => -1) 1 x.val = 0 ∧ foldedOdo 1 4 (fun _ => -1) 1 x = 0 := by
  have h := (symmetry_lemma 1 4 (fun _ => -1) (fun _ _ _ _ => rfl)).2 1 x
  have hf : foldedOdo 1 4 (fun _ => -1) 1 x = 0 := by
    rw [foldedOdo_one]; norm_num
  exact ⟨h.trans hf, hf⟩

example (x : SimplexSite 1 (sideHalf 4)) :
    odo 1 4 (fun _ => 4) 1 x.val = 1 ∧ foldedOdo 1 4 (fun _ => 4) 1 x = 1 := by
  have h := (symmetry_lemma 1 4 (fun _ => 4) (fun _ _ _ _ => rfl)).2 1 x
  have hf : foldedOdo 1 4 (fun _ => 4) 1 x = 1 := by
    rw [foldedOdo_one]; norm_num
  exact ⟨h.trans hf, hf⟩

-- Only the values inside the cube are symmetric; the exterior is coordinate-dependent.
example (t : ℕ) (x : SimplexSite 1 (sideHalf 4)) :
    odo 1 4 (fun y => if inCube 1 4 y then 4 else y 0) t x.val =
      foldedOdo 1 4 (fun y => if inCube 1 4 y then 4 else y 0) t x := by
  apply (symmetry_lemma 1 4 _ ?_).2 t x
  intro π ε y hy
  simp only [ite_eq_left hy, ite_eq_left ((cubeSym_inCube 1 4 π ε y).2 hy)]

-- Odd reflection sends 0 to 2; even reflection sends 0 to 1.
example : foldPointN 1 3 (fun _ => 0) = (fun _ => 2) := by
  funext i
  norm_num [foldPointN, cubeSym, loCoord, hiCoord, sideHalf]
example : foldPointN 1 4 (fun _ => 0) = (fun _ => 1) := by
  funext i
  norm_num [foldPointN, cubeSym, loCoord, hiCoord, sideHalf]

private abbrev oneSite (N a : ℕ) (h : inSimplex 1 (sideHalf N) (fun _ => (a : ℤ))) :
    SimplexSite 1 (sideHalf N) := ⟨fun _ => (a : ℤ), h⟩

private theorem oneSite_mem (N a : ℕ) (ha : 1 ≤ a) (hN : a ≤ sideHalf N) :
    inSimplex 1 (sideHalf N) (fun _ => (a : ℤ)) := by
  constructor
  · intro i
    change (1 : ℤ) ≤ (a : ℤ) ∧ (a : ℤ) ≤ (sideHalf N : ℤ)
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hN⟩
  · exact fun _ _ _ => le_rfl

-- On the odd cube N=3 the two neighbors of 1 BOTH represent 2.
-- Keeping two summands detects accidental deduplication.
example (v : SimplexSite 1 (sideHalf 3) → ℤ) :
    foldedNbrSum 1 3 v (oneSite 3 1 (oneSite_mem 3 1 (by decide) (by decide))) =
      2 * v (oneSite 3 2 (oneSite_mem 3 2 (by decide) (by decide))) := by
  have hp : ∀ π : Equiv.Perm (Fin 1), π = Equiv.refl (Fin 1) := fun _ => Subsingleton.elim _ _
  have hy0 : inCube 1 3 (fun _ => 0) := by decide
  have hy2 : inCube 1 3 (fun _ => 2) := by decide
  have hadd : (fun _ : Fin 1 => (1 : ℤ)) + unit (0 : Fin 1) = (fun _ => 2) := by
    ext i; fin_cases i; norm_num [unit]
  have hsub : (fun _ : Fin 1 => (1 : ℤ)) - unit (0 : Fin 1) = (fun _ => 0) := by
    ext i; fin_cases i; norm_num [unit]
  simp only [foldedNbrSum, Fin.sum_univ_one]
  change foldedLift 1 3 v ((fun _ => (1 : ℤ)) + unit (0 : Fin 1)) +
    foldedLift 1 3 v ((fun _ => (1 : ℤ)) - unit (0 : Fin 1)) = _
  rw [hadd, hsub, foldedLift_of_inCube 1 3 v _ hy0, foldedLift_of_inCube 1 3 v _ hy2]
  have hrep0 : toSimplexPointN 1 3 (fun _ => 0) = (fun _ => 2) := by
    funext i
    norm_num [toSimplexPointN, hp, foldPointN, cubeSym, loCoord, hiCoord, sideHalf]
  have hrep2 : toSimplexPointN 1 3 (fun _ => 2) = (fun _ => 2) := by
    funext i
    norm_num [toSimplexPointN, hp, foldPointN, cubeSym]
  have he0 : (⟨toSimplexPointN 1 3 (fun _ => 0), inSimplex_toSimplexPointN 1 3 _ hy0⟩ :
      SimplexSite 1 (sideHalf 3)) = oneSite 3 2 (oneSite_mem 3 2 (by decide) (by decide)) :=
    Subtype.ext hrep0
  have he2 : (⟨toSimplexPointN 1 3 (fun _ => 2), inSimplex_toSimplexPointN 1 3 _ hy2⟩ :
      SimplexSite 1 (sideHalf 3)) = oneSite 3 2 (oneSite_mem 3 2 (by decide) (by decide)) :=
    Subtype.ext hrep2
  rw [he0, he2]
  ring

-- N=1 has a genuine physical site and both directed neighbors dissipate.
example (v : SimplexSite 1 (sideHalf 1) → ℤ) :
    foldedNbrSum 1 1 v (oneSite 1 1 (oneSite_mem 1 1 (by decide) (by decide))) = 0 := by
  have houtp : ¬ inCube 1 1 ((fun _ => 1) + unit (0 : Fin 1)) := by decide
  have houtm : ¬ inCube 1 1 ((fun _ => 1) - unit (0 : Fin 1)) := by decide
  simp only [foldedNbrSum, Fin.sum_univ_one]
  change foldedLift 1 1 v ((fun _ => (1 : ℤ)) + unit (0 : Fin 1)) +
    foldedLift 1 1 v ((fun _ => (1 : ℤ)) - unit (0 : Fin 1)) = 0
  rw [foldedLift_of_not_inCube 1 1 v _ houtp, foldedLift_of_not_inCube 1 1 v _ houtm,
    add_zero]

example (t : ℕ) : odo 1 1 (fun _ => 4) t (fun _ => 1) =
    foldedOdo 1 1 (fun _ => 4) t (oneSite 1 1 (oneSite_mem 1 1 (by decide) (by decide))) :=
  (symmetry_lemma 1 1 (fun _ => 4) (fun _ _ _ _ => rfl)).2 t
    (oneSite 1 1 (oneSite_mem 1 1 (by decide) (by decide)))

-- A real radial consumer: transfer the physical radial neighbor ledger to
-- the independently defined folded process, including k=0 and k=d.
private def radialSite (d k : ℕ) : SimplexSite d (sideHalf 4) :=
  ⟨radial d k, by
    constructor
    · intro i
      simp only [radial, sideHalf]
      split <;> norm_num
    · intro i j hij
      simp only [radial]
      split <;> split <;> omega⟩

example (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    foldedNbrSum d 4 (foldedOdo d 4 (fun _ => c) t) (radialSite d k) =
      (k : ℤ) * foldedOdo d 4 (fun _ => c) t (radialSite d (k - 1)) +
        ((d : ℤ) - (k : ℤ)) *
          (foldedOdo d 4 (fun _ => c) t (radialSite d (k + 1)) +
            foldedOdo d 4 (fun _ => c) t (radialSite d k)) := by
  have hsym : CubeSymmetric d 4 (fun _ => c) := fun _ _ _ _ => rfl
  have hlift : foldedLift d 4 (foldedOdo d 4 (fun _ => c) t) =
      odo d 4 (fun _ => c) t := funext (foldedLift_foldedOdo d 4 (fun _ => c) hsym t)
  rw [foldedNbrSum_eq_nbrSum, hlift]
  have hid (j : ℕ) : odo d 4 (fun _ => c) t (radial d j) =
      foldedOdo d 4 (fun _ => c) t (radialSite d j) :=
    (symmetry_lemma d 4 (fun _ => c) hsym).2 t (radialSite d j)
  change nbrSum (odo d 4 (fun _ => c) t) (radial d k) = _
  rw [nbrSum_radial d c t k hk, hid (k - 1), hid (k + 1), hid k]



example : odo 1 4 (fun _ => -1) 1 (fun _ => 1) = 0 := by
  have h := (symmetry_lemma 1 4 (fun _ => -1) (fun _ _ _ _ => rfl)).2 1
    (oneSite 4 1 (oneSite_mem 4 1 (by decide) (by decide)))
  rw [foldedOdo_one] at h
  exact h.trans (by norm_num)

example : odo 1 4 (fun _ => 4) 1 (fun _ => 1) = 1 := by
  have h := (symmetry_lemma 1 4 (fun _ => 4) (fun _ _ _ _ => rfl)).2 1
    (oneSite 4 1 (oneSite_mem 4 1 (by decide) (by decide)))
  rw [foldedOdo_one] at h
  exact h.trans (by norm_num)

example (t : ℕ) : odo 1 3 (fun _ => 4) t (fun _ => 1) =
    foldedOdo 1 3 (fun _ => 4) t (oneSite 3 1 (oneSite_mem 3 1 (by decide) (by decide))) :=
  (symmetry_lemma 1 3 (fun _ => 4) (fun _ _ _ _ => rfl)).2 t
    (oneSite 3 1 (oneSite_mem 3 1 (by decide) (by decide)))

-- The dimension-zero case is covered by the exact unrestricted statement.
example (t : ℕ) : odo 0 0 (fun _ => 0) t (fun i => Fin.elim0 i) =
    foldedOdo 0 0 (fun _ => 0) t
      ⟨(fun i => Fin.elim0 i), ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩⟩ :=
  (symmetry_lemma 0 0 (fun _ => 0) (fun _ _ _ _ => rfl)).2 t
    ⟨(fun i => Fin.elim0 i), ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩⟩

end ReflectedThresholdAcceptance
