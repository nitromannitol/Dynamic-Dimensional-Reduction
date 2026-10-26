module

public import DimRed.Support.Fundamental
public import DimRed.Support.SnocSimplex
public import DimRed.Support.TerminalReduction

@[expose] public section

/-!
# Physical carriers for the corrected source API

Piles are evaluated on the physical cube, terminal piles require positive
dimension, and maxima require a nonempty simplex. The geometric constructors
retain their literal coordinates. Uniform stabilization identifies the terminal
pile with the actual finite-time pile after a single global time.
-/

namespace DimRed.Corrected

open LatticeProb

/-- A physical site of the cube of side `N`. -/
abbrev CubeSite (d N : ℕ) := {x : Site d // inCube d N x}

/-- A site in the sorted positive fundamental domain. -/
abbrev SimplexSite (d M : ℕ) := {x : Site d // inSimplex d M x}

/-- Symmetry requires agreement of initial values only on the physical cube. -/
def CubeSymmetric (d N : ℕ) (s₀ : Site d → ℤ) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d),
    inCube d N x → s₀ (cubeSym d N π ε x) = s₀ x

/-- The finite-time source pile on its physical carrier. -/
def pile (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : CubeSite d N) : ℤ :=
  s₀ x.val + lap (odo d N s₀ t) x.val

/-- The uniform terminal source pile in positive dimension. -/
noncomputable def terminalPile (d N : ℕ) (_hd : 1 ≤ d) (x : CubeSite d N) : ℤ :=
  2 * (d : ℤ) + lap (fun y => ((odoInfUnif d N y).toNat : ℤ)) x.val

/-- The maximum on a genuinely nonempty fundamental domain. -/
noncomputable def maximum (d M : ℕ) (hne : (simplex d M).Nonempty)
    (f : Site d → ℤ) : ℤ :=
  (simplex d M).sup' hne f

/-- The literal all-ones point witnesses nonemptiness, also in dimension zero. -/
theorem simplexNonempty (d M : ℕ) (hM : 1 ≤ M) : (simplex d M).Nonempty := by
  refine ⟨(fun _ => 1), (mem_simplex_iff d M _).2 ?_⟩
  constructor
  · intro i
    change (1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ (M : ℤ)
    exact ⟨le_rfl, by exact_mod_cast hM⟩
  · intro i j hij
    exact le_rfl

theorem simplex_inCube (d N : ℕ) (x : Site d)
    (hx : inSimplex d (sideHalf N) x) : inCube d N x := by
  intro i
  have hi := hx.1 i
  simp only [loCoord, hiCoord]
  exact ⟨by omega, hi.2⟩

/-- A simplex site, with its original coordinates, viewed in the physical cube. -/
def cubeSimplexSite (d N : ℕ) (_hN : 1 ≤ N)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) : CubeSite d N :=
  ⟨x, simplex_inCube d N x hx⟩

/-- Append the literal coordinate `1` to a simplex site. -/
def cubeSnocOne (d N : ℕ) (hN : 1 ≤ N)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) : CubeSite (d + 1) N :=
  ⟨Fin.snoc x 1, (inCube_snoc x 1).2 ⟨simplex_inCube d N x hx,
    by simp only [loCoord]; omega,
    by simp only [hiCoord, sideHalf]; omega⟩⟩

/-- The source translation into the smaller physical cube. -/
def cubeShiftedSite (N d j : ℕ) (_hN : 1 ≤ N) (_hd : 1 ≤ d)
    (_hj : j < sideHalf N) (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) : CubeSite d (2 * j) :=
  ⟨(fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))), by
    intro i
    rw [loCoord_two_mul, hiCoord_two_mul]
    dsimp only
    have hi := hx.1 i
    have hgt := hxgt i
    constructor <;> omega⟩

@[simp] theorem cubeSimplexSite_val (d N : ℕ) (hN : 1 ≤ N)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    (cubeSimplexSite d N hN x hx).val = x := rfl

@[simp] theorem cubeSnocOne_val (d N : ℕ) (hN : 1 ≤ N)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) :
    (cubeSnocOne d N hN x hx).val = Fin.snoc x 1 := rfl

@[simp] theorem cubeShiftedSite_val (N d j : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (hj : j < sideHalf N) (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i) :
    (cubeShiftedSite N d j hN hd hj x hx hxgt).val =
      fun i => x i - ((sideHalf N : ℤ) - (j : ℤ)) := rfl

/-- Existing finite-time pile expressions agree on every physical site. -/
theorem pile_eq_sandp (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : CubeSite d N) :
    pile d N s₀ t x = sandp d N s₀ t x.val := rfl

/-- This bridge is only an expression equality on the positive-dimensional carrier. -/
theorem terminalPile_eq_sandpInfUnif (d N : ℕ) (hd : 1 ≤ d) (x : CubeSite d N) :
    terminalPile d N hd x = sandpInfUnif d N x.val := rfl

theorem maximum_eq_sup' (d M : ℕ) (hne : (simplex d M).Nonempty)
    (f : Site d → ℤ) : maximum d M hne f = (simplex d M).sup' hne f := rfl

/-- The old maximum agrees with `maximum` under the nonemptiness hypothesis `hne`. -/
theorem maximum_eq_simplexMax (d M : ℕ) (hne : (simplex d M).Nonempty)
    (f : Site d → ℤ) : maximum d M hne f = simplexMax d M f := by
  simp only [maximum, simplexMax, dite_eq_left hne]

theorem le_maximum (d M : ℕ) (hne : (simplex d M).Nonempty) (f : Site d → ℤ)
    (x : SimplexSite d M) : f x.val ≤ maximum d M hne f := by
  exact Finset.le_sup' f ((mem_simplex_iff d M x.val).2 x.property)

theorem maximum_le (d M : ℕ) (hne : (simplex d M).Nonempty) (f : Site d → ℤ)
    (c : ℤ) (h : ∀ x : SimplexSite d M, f x.val ≤ c) : maximum d M hne f ≤ c := by
  exact Finset.sup'_le hne f fun x hx => h ⟨x, (mem_simplex_iff d M x).1 hx⟩

private theorem uniform_stabilizes (d N : ℕ) (hd : 1 ≤ d) :
    ∃ T, odo d N (fun _ => 2 * (d : ℤ)) (T + 1) =
      odo d N (fun _ => 2 * (d : ℤ)) T := by
  apply odoInf_finite d N hd
  · intro y hy
    positivity
  · intro y hy
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega

/-- No terminal odometer value converted by `terminalPile` is infinite. -/
theorem odoInfUnif_ne_top (d N : ℕ) (hd : 1 ≤ d) (y : Site d) :
    odoInfUnif d N y ≠ ⊤ := by
  obtain ⟨T, hT⟩ := uniform_stabilizes d N hd
  change odoInf d N (fun _ => 2 * (d : ℤ)) y ≠ ⊤
  rw [odoInf_eq_of_stable d N (fun _ => 2 * (d : ℤ)) T hT y]
  exact ENat.natCast_ne_top _

/-- After stabilization the literal terminal pile is the finite-time pile. -/
theorem terminalPile_eventually (d N : ℕ) (hd : 1 ≤ d) (x : CubeSite d N) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      terminalPile d N hd x = pile d N (fun _ => 2 * (d : ℤ)) t x := by
  obtain ⟨T, hT⟩ := uniform_stabilizes d N hd
  have hterminal : (fun y => ((odoInfUnif d N y).toNat : ℤ)) =
      odo d N (fun _ => 2 * (d : ℤ)) T := by
    funext y
    change ((odoInf d N (fun _ => 2 * (d : ℤ)) y).toNat : ℤ) = _
    rw [odoInf_eq_of_stable d N (fun _ => 2 * (d : ℤ)) T hT y, ENat.toNat_natCast,
      Int.toNat_of_nonneg (odo_nonneg d N (fun _ => 2 * (d : ℤ)) T y)]
  refine ⟨T, fun t ht => ?_⟩
  have htT : odo d N (fun _ => 2 * (d : ℤ)) t =
      odo d N (fun _ => 2 * (d : ℤ)) T := by
    have h := odo_const_of_stable d N (fun _ => 2 * (d : ℤ)) T hT (t - T)
    simpa only [Nat.add_sub_of_le ht] using h
  unfold terminalPile pile
  rw [hterminal, htT]

/-- Consumer of `terminalPile_eventually` at `d = 2`, `N = 4` and the cube site `(1, 1)`: the
literal terminal pile equals the finite-time pile for all large `t`. -/
theorem terminalPile_eventually_cube_site :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      terminalPile 2 4 (by norm_num) ⟨![1, 1], by decide⟩ =
        pile 2 4 (fun _ => 2 * ((2 : ℕ) : ℤ)) t ⟨![1, 1], by decide⟩ :=
  terminalPile_eventually 2 4 (by norm_num) ⟨![1, 1], by decide⟩

/-- Consumer of `maximum_eq_simplexMax` with `simplexNonempty` at `d = 2`, `M = 2`: the
nonempty maximum agrees with the old `simplexMax`. -/
theorem maximum_eq_simplexMax_simplex_two (f : Site 2 → ℤ) :
    maximum 2 2 (simplexNonempty 2 2 (by norm_num)) f = simplexMax 2 2 f :=
  maximum_eq_simplexMax 2 2 (simplexNonempty 2 2 (by norm_num)) f

end DimRed.Corrected
