/-
The general-scale iteration for Theorem 1.1(ii), together with the odd-side
coordinate reflection.  The self-similarity argument is the iteration of the
consecutive-scale step in the statement labelled `the_theorem` in `dimred-corrected-arxiv.tex`; its scale bridge and its
`toppleTime` bounds are explicit because the consecutive step is stated only
for even side lengths.  The odd reflection is the boundary adjustment
described in the subsection titled `Notation and conventions` in `dimred-corrected-arxiv.tex`, in the section labelled `subsec:symmetry` of
`dimred-corrected-arxiv.tex`, and in `dimred-corrected-arxiv.tex`, label `subsec:symmetry`.
-/
import DimRed.Support.AxisStep

namespace DimRed

open LatticeProb

/-- The consecutive-scale self-similarity step iterates from `sideHalf N` to
`j`.  The hypothesis `hscale` is the bridge from an arbitrary box `N` to the
even box `2 * sideHalf N`; `htime` records exactly the toppling-time bounds
needed at every scale used by the iteration. -/
theorem self_similarity_main (N d : ℕ) (_hN : 1 ≤ N) (_hd : 2 ≤ d)
    (j : ℕ) (hj : j < sideHalf N) (t : ℕ)
    (_ht : (t : ℕ∞) ≤ toppleTime d j)
    (x : Site d) (hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i)
    (hscale : odoUnif d N t x = odoUnif d (2 * sideHalf N) t x)
    (hstep : ∀ m : ℕ, j < m → m ≤ sideHalf N →
      ∀ y : Site d, inSimplex d m y → (∀ i, 1 < y i) →
        odoUnif d (2 * m) t y =
          odoUnif d (2 * (m - 1)) t (fun i => y i - 1)) :
    odoUnif d N t x = odoUnif d (2 * j) t
      (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  let M : ℕ := sideHalf N
  have hjM : j < M := by
    simpa [M] using hj
  have hxM : inSimplex d M x := by
    simpa [M] using hx
  have hxgtM : ∀ i, (M : ℤ) - (j : ℤ) < x i := by
    simpa [M] using hxgt
  have hjM_le : j ≤ M := Nat.le_of_lt hjM
  have hMsub_cast : ((M - j : ℕ) : ℤ) = (M : ℤ) - (j : ℤ) := by
    rw [Nat.cast_sub hjM_le]
  have hsimplex : ∀ k : ℕ, k ≤ M - j →
      inSimplex d (M - k) (fun i => x i - (k : ℤ)) := by
    intro k hk
    have hkz : (k : ℤ) ≤ (M : ℤ) - (j : ℤ) := by
      rw [← hMsub_cast]
      exact_mod_cast hk
    constructor
    · intro i
      have hxi := hxM.1 i
      have hxgti := hxgtM i
      constructor <;> dsimp <;> omega
    · intro i l hil
      have hxl := hxM.2 i l hil
      dsimp
      omega
  have hiter : ∀ k : ℕ, k ≤ M - j →
      odoUnif d (2 * M) t x =
        odoUnif d (2 * (M - k)) t (fun i => x i - (k : ℤ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        have hkprev : k ≤ M - j := by omega
        have hkM : k < M := by omega
        have hmj : j < M - k := by omega
        have hmM : M - k ≤ M := Nat.sub_le _ _
        have hy : inSimplex d (M - k) (fun i => x i - (k : ℤ)) :=
          hsimplex k hkprev
        have hygt : ∀ i, 1 < x i - (k : ℤ) := by
          intro i
          have hxi := hxgtM i
          omega
        have hs := hstep (M - k) hmj hmM
          (fun i => x i - (k : ℤ)) hy hygt
        have hscale_step : (M - k) - 1 = M - (k + 1) := by omega
        have hpoint_step :
            (fun i => (x i - (k : ℤ)) - 1) =
              (fun i => x i - ((k + 1 : ℕ) : ℤ)) := by
          funext i
          push_cast
          ring
        rw [hscale_step, hpoint_step] at hs
        exact (ih hkprev).trans hs
  have hfinal := hiter (M - j) (le_rfl)
  have hscale_final : M - (M - j) = j := by omega
  have hpoint_final :
      (fun i => x i - ((M - j : ℕ) : ℤ)) =
        (fun i => x i - ((M : ℤ) - (j : ℤ))) := by
    funext i
    congr 1
  rw [hscale_final, hpoint_final] at hfinal
  exact hscale.trans (by simpa [M] using hfinal)

/-- Reflection in the fixed site hyperplane `u_i = 1` for an odd box. -/
theorem odo_reflect_coord_odd (d N : ℕ) (hNodd : N % 2 = 1) (c : ℤ) (t : ℕ)
    (u : Site d) (i : Fin d) :
    odo d N (fun _ => c) t (fun k => if k = i then 2 - u i else u k) =
      odo d N (fun _ => c) t u := by
  have hsum : loCoord N + hiCoord N = 2 := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, N = 2 * m + 1 := by
      have hdiv := Nat.mod_add_div N 2
      rw [hNodd] at hdiv
      exact ⟨N / 2, by omega⟩
    rw [hm]
    unfold loCoord hiCoord sideHalf
    have hdiv1 : (2 * m + 1) / 2 = m := by omega
    have hdiv2 : ((2 * m + 1) + 1) / 2 = m + 1 := by omega
    rw [hdiv1, hdiv2]
    push_cast
    ring
  have h := odo_cubeSym d N (fun _ => c) (isSymmetricPile_const' d N c) t
    (Equiv.refl (Fin d)) (fun k => if k = i then false else true) u
  have heq : cubeSym d N (Equiv.refl (Fin d))
      (fun k => if k = i then false else true) u =
      (fun k => if k = i then 2 - u i else u k) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [cubeSym, hsum]
    · simp [cubeSym, hk]
  rwa [heq] at h

end DimRed
