module

/-
The symmetries of the hypercube and the invariance of the odometer under them:
`cubeSym` carries a neighbour step of `σ x` to a neighbour step of `x`, so the
neighbour sum and the Laplacian commute with `σ`, and Lemma 2.3 follows by
induction on the time.
-/
public import DimRed.Support.Recursion

@[expose] public section

namespace DimRed

open LatticeProb

open LatticeProb

theorem symStep_apply (d : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i j : Fin d) :
    symStep π ε i (π j) = (if j = i then (if ε i then (1 : ℤ) else -1) else 0) := by
  have hpi : j ≠ i → π j ≠ π i := fun hj h => hj (π.injective h)
  by_cases he : ε i
  · simp only [symStep, ite_eq_left he, unit]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hpi hj, hj]
  · simp only [symStep, ite_eq_right he, Pi.neg_apply, unit]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hpi hj, hj]

theorem cubeSym_add (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (x : Site d) (i : Fin d) :
    cubeSym d N π ε x + unit i = cubeSym d N π ε (x + symStep π ε i) := by
  funext j
  simp only [cubeSym, Pi.add_apply, unit, Pi.single_apply, symStep_apply]
  by_cases hj : j = i
  · subst hj
    by_cases he : ε j
    · simp [he]
    · simp [he]; ring_nf
  · simp [hj]

theorem cubeSym_sub (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (x : Site d) (i : Fin d) :
    cubeSym d N π ε x - unit i = cubeSym d N π ε (x - symStep π ε i) := by
  funext j
  simp only [cubeSym, Pi.sub_apply, unit, Pi.single_apply, symStep_apply]
  by_cases hj : j = i
  · subst hj
    by_cases he : ε j
    · simp [he]
    · simp [he]; ring_nf
  · simp [hj]

theorem cubeSym_inCube (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) :
    inCube d N (cubeSym d N π ε x) ↔ inCube d N x := by
  constructor
  · intro h i
    have hj := h (π.symm i)
    simp only [cubeSym, Equiv.apply_symm_apply] at hj
    by_cases he : ε (π.symm i) <;> simp only [he, ite_true] at hj <;>
      omega
  · intro h j
    simp only [cubeSym]
    have hj := h (π j)
    by_cases he : ε j <;> simp only [he, ite_true] <;> omega

theorem nbrSum_cubeSym (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (u : Site d → ℤ) (hu : ∀ y, u (cubeSym d N π ε y) = u y) (x : Site d) :
    nbrSum u (cubeSym d N π ε x) = nbrSum u x := by
  have step : ∀ i : Fin d,
      u (cubeSym d N π ε x + unit i) + u (cubeSym d N π ε x - unit i)
        = u (x + unit (π i)) + u (x - unit (π i)) := by
    intro i
    rw [cubeSym_add, cubeSym_sub, hu, hu]
    by_cases he : ε i
    · simp [symStep, he]
    · simp [symStep, he]
      ring_nf
  simp only [nbrSum, step]
  exact Equiv.sum_comp π (fun j => u (x + unit j) + u (x - unit j))

theorem odo_cubeSym (d N : ℕ) (s₀ : Site d → ℤ) (hsym : IsSymmetricPile d N s₀)
    (t : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) :
    odo d N s₀ t (cubeSym d N π ε x) = odo d N s₀ t x := by
  induction t generalizing x with
  | zero => rfl
  | succ n ih =>
    have hnb : nbrSum (odo d N s₀ n) (cubeSym d N π ε x) = nbrSum (odo d N s₀ n) x :=
      nbrSum_cubeSym d N π ε _ (fun y => ih y) x
    have hlap : lap (odo d N s₀ n) (cubeSym d N π ε x) = lap (odo d N s₀ n) x := by
      simp only [lap, hnb, ih x]
    simp only [odo, cubeSym_inCube, hlap, ih x, hsym π ε x]

end DimRed
