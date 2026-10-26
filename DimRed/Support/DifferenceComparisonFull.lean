module

public import DimRed.Support.Difference
public import DimRed.Support.Symmetry

@[expose] public section

/-!
Difference comparison for arbitrary constant integer initial heights. The proof
uses the physical threshold update: a strict old difference has an integer
margin, and at equality the neighbour-sum inequality orders the firing tests.
The first boundary alternative retains translated physical-cube membership.
-/

namespace DimRed.Corrected

open LatticeProb

/-- One physical update preserves a difference bound when the neighbour sums
satisfy the corresponding bound. No bound on the initial height is needed. -/
private theorem difference_threshold_step (d N : ℕ) (c a : ℤ) (t : ℕ)
    (x y : Site d) (hx : inCube d N x) (hy : inCube d N y)
    (hprev : odo d N (fun _ => c) t x - odo d N (fun _ => c) t y - a ≤ 0)
    (hsum : nbrSum (odo d N (fun _ => c) t) x -
      nbrSum (odo d N (fun _ => c) t) y - 2 * (d : ℤ) * a ≤ 0) :
    odo d N (fun _ => c) (t + 1) x -
      odo d N (fun _ => c) (t + 1) y - a ≤ 0 := by
  by_cases hlt : odo d N (fun _ => c) t x - odo d N (fun _ => c) t y < a
  · have hxstep := odo_succ_sub_bounds d N (fun _ => c) t x
    have hystep := odo_succ_sub_bounds d N (fun _ => c) t y
    omega
  · have heq : odo d N (fun _ => c) t x = odo d N (fun _ => c) t y + a := by
      omega
    have hsand : sandp d N (fun _ => c) t x ≤ sandp d N (fun _ => c) t y := by
      dsimp only [sandp, lap]
      rw [heq]
      nlinarith only [hsum]
    rw [odo_succ_eq d N (fun _ => c) t x hx,
      odo_succ_eq d N (fun _ => c) t y hy]
    by_cases hfire : 2 * (d : ℤ) ≤ sandp d N (fun _ => c) t x
    · rw [ite_eq_left hfire, ite_eq_left (le_trans hfire hsand)]
      omega
    · rw [ite_eq_right hfire]
      split_ifs <;> omega

/-- Simultaneous difference comparison on the sorted domain, for every
constant integer height and with physical membership in the first boundary
alternative. -/
theorem general_difference_comparison (d M : ℕ) (_hd : 1 ≤ d) (c : ℤ)
    {n : ℕ} (w : Fin n → Site d) (g : Fin n → Site d → ℤ)
    (hg : ∀ k, SuperharmonicIn d M (g k)) (t₀ : ℕ)
    (hinit : ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) t₀ x - odo d (2 * M) (fun _ => c) t₀ (x + w k) - g k x ≤ 0)
    (hbdry : ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → (bdry M 0 x ∨ ∃ k, bdry M (w k) x) →
      ((∀ k, inCube d (2 * M) (x + w k) ∧
          nbrSum (odo d (2 * M) (fun _ => c) t) x
          - nbrSum (odo d (2 * M) (fun _ => c) t) (x + w k) - 2 * (d : ℤ) * g k x ≤ 0) ∨
       (∀ k, odo d (2 * M) (fun _ => c) (t + 1) x
          - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0))) :
    ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) (t + 1) x
        - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0 := by
  have hmain : ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) t x -
        odo d (2 * M) (fun _ => c) t (x + w k) - g k x ≤ 0 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hinit
    | succ t ht ih =>
      intro x hx k
      by_cases hb : bdry M 0 x ∨ ∃ k, bdry M (w k) x
      · rcases hbdry t ht x hx hb with hsum | hnext
        · exact difference_threshold_step d (2 * M) c (g k x) t x (x + w k)
            (inSimplex_inCube d M x hx) (hsum k).1 (ih x hx k) (hsum k).2
        · exact hnext k
      · have hstrict : (∀ i : Fin d, x i < (M : ℤ)) ∧
            (∀ i : Fin d, 1 < x i) ∧
            (∀ i j : Fin d, i < j → x j < x i) := by
          simpa only [add_zero] using
            not_bdry_strict M 0 x (fun h => hb (Or.inl h))
        have hstrictw := not_bdry_strict M (w k) x (fun h => hb (Or.inr ⟨k, h⟩))
        have hxnb : ∀ i : Fin d,
            inSimplex d M (x + unit i) ∧ inSimplex d M (x - unit i) :=
          fun i => ⟨inSimplex_add_unit d M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i,
            inSimplex_sub_unit d M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i⟩
        have hxw : inSimplex d M (x + w k) :=
          inSimplex_of_strict M (x + w k) hstrictw.1 hstrictw.2.1 hstrictw.2.2
        have hsum : nbrSum (odo d (2 * M) (fun _ => c) t) x -
            nbrSum (odo d (2 * M) (fun _ => c) t) (x + w k) ≤ nbrSum (g k) x := by
          rw [← nbrSum_shift (odo d (2 * M) (fun _ => c) t) x (w k), ← nbrSum_sub]
          unfold nbrSum
          refine Finset.sum_le_sum fun i _ => ?_
          have hp := ih (x + unit i) (hxnb i).1 k
          have hm := ih (x - unit i) (hxnb i).2 k
          dsimp only
          omega
        have hsuper := hg k x hx hxnb
        apply difference_threshold_step d (2 * M) c (g k x) t x (x + w k)
          (inSimplex_inCube d M x hx) (inSimplex_inCube d M (x + w k) hxw) (ih x hx k)
        omega
  intro t ht x hx k
  exact hmain (t + 1) (Nat.le_trans ht (Nat.le_succ t)) x hx k

end DimRed.Corrected

namespace DimRed.Corrected

open LatticeProb

/-! Acceptance applications. The two shifts below are distinct: index zero is
the identity and index one crosses the reflecting face from 1 to 0. Both
translated sites are physical. The simultaneous first boundary alternative
is proved from symmetry, for every time and every integer height. -/

private theorem two_index_boundary_application (c : ℤ) (t : ℕ) (k : Fin 2) :
    odo 1 2 (fun _ => c) (t + 1) (fun _ => 1) -
      odo 1 2 (fun _ => c) (t + 1)
        ((fun _ => 1) + (fun _ => -(k : ℤ))) ≤ 0 := by
  have hsym : IsSymmetricPile 1 2 (fun _ => c) := fun _ _ _ => rfl
  have hreflect (s : ℕ) :
      nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 0) =
        nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 1) := by
    have h := nbrSum_cubeSym 1 2 (Equiv.refl _) (fun _ => false)
      (odo 1 2 (fun _ => c) s)
      (fun y => odo_cubeSym 1 2 (fun _ => c) hsym s
        (Equiv.refl _) (fun _ => false) y) (fun _ => 1)
    have hpt : cubeSym 1 2 (Equiv.refl _) (fun _ => false) (fun _ => (1 : ℤ)) =
        fun _ => (0 : ℤ) := by
      funext i
      simp [cubeSym, loCoord, hiCoord, sideHalf]
    rw [hpt] at h
    exact h
  have h := general_difference_comparison 1 1 (by omega) c
    (fun j : Fin 2 => fun _ => -(j : ℤ)) (fun _ _ => 0)
    (by intro _ _ _ _; norm_num [nbrSum]) 0
    (by intro _ _ _; norm_num [odo])
    (by
      intro s _ x hx _
      have hx1 : x = fun _ => 1 := by
        funext i
        exact le_antisymm (hx.1 i).2 (hx.1 i).1
      rw [hx1]
      left
      intro j
      fin_cases j
      · constructor
        · intro i
          norm_num [loCoord, hiCoord, sideHalf]
        · change nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 1) -
            nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 1) - 2 * (1 : ℤ) * 0 ≤ 0
          omega
      · constructor
        · intro i
          norm_num [loCoord, hiCoord, sideHalf]
        · change nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 1) -
            nbrSum (odo 1 2 (fun _ => c) s) (fun _ => 0) - 2 * (1 : ℤ) * 0 ≤ 0
          rw [hreflect s]
          omega)
    t (Nat.zero_le t) (fun _ => 1)
    (by constructor <;> intros <;> norm_num) k
  simpa only [sub_zero] using h

-- Negative height, with both indices active in the application.
example (t : ℕ) (k : Fin 2) :
    odo 1 2 (fun _ => (-1 : ℤ)) (t + 1) (fun _ => 1) -
      odo 1 2 (fun _ => (-1 : ℤ)) (t + 1)
        ((fun _ => 1) + (fun _ => -(k : ℤ))) ≤ 0 :=
  two_index_boundary_application (-1) t k

-- Height 4 exceeds the old upper bound 4d-1=3 in dimension one.
example (t : ℕ) (k : Fin 2) :
    odo 1 2 (fun _ => (4 : ℤ)) (t + 1) (fun _ => 1) -
      odo 1 2 (fun _ => (4 : ℤ)) (t + 1)
        ((fun _ => 1) + (fun _ => -(k : ℤ))) ≤ 0 :=
  two_index_boundary_application 4 t k

-- The examples use the physical threshold update: zero for -1, one for 4.
example : odo 1 2 (fun _ => (-1 : ℤ)) 1 (fun _ => 1) = 0 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

example : odo 1 2 (fun _ => (4 : ℤ)) 1 (fun _ => 1) = 1 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum]

-- CE-BOUNDARY has x=2, w=1 in C_4. Its translated site is not physical,
-- so the corrected first boundary alternative explicitly excludes it.
example : ¬ inCube 1 4 ((fun _ => (2 : ℤ)) + (fun _ => (1 : ℤ))) := by
  intro h
  have htop := (h 0).2
  norm_num [hiCoord, sideHalf] at htop

example : odo 1 4 (fun _ => (2 : ℤ)) 3 (fun _ => 2) -
    odo 1 4 (fun _ => (2 : ℤ)) 3 (fun _ => 3) = 2 := by
  norm_num [odo, inCube, loCoord, hiCoord, sideHalf, lap, nbrSum, unit]

end DimRed.Corrected
