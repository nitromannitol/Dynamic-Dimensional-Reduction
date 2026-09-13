/-
The one-dimensional radial computations of `dimred.tex:958-1024`: reflection
about the centre of the interval `C_{2M}^{(1)}`, and the Laplacian at the two
sites of `S_2^{(1)}`.
-/
import DimRed.Support.Radial

namespace DimRed

open LatticeProb

theorem loCoord_add_hiCoord_two_mul (M : ℕ) :
    loCoord (2 * M) + hiCoord (2 * M) = 1 := by
  rw [loCoord, hiCoord, sideHalf]
  have h1 : 2 * M / 2 = M := by omega
  have h2 : (2 * M + 1) / 2 = M := by omega
  rw [h1, h2]
  ring

theorem odo_reflect_d1 (M t : ℕ) (y : Site 1) :
    odo 1 (2 * M) (fun _ => 2) t (fun i => 1 - y i) = odo 1 (2 * M) (fun _ => 2) t y := by
  have hsym := isSymmetricPile_const 1 (2 * M) 2
  have h := odo_cubeSym 1 (2 * M) (fun _ => 2) hsym t (Equiv.refl (Fin 1))
    (fun _ => false) y
  have e : cubeSym 1 (2 * M) (Equiv.refl (Fin 1)) (fun _ => false) y
      = fun i => 1 - y i := by
    funext i
    simp only [cubeSym, Equiv.refl_apply]
    rw [if_neg (by decide : ¬ (false = true)), loCoord_add_hiCoord_two_mul]
  rwa [e] at h

theorem lap_radial_d1 (M t : ℕ) (_hM : 2 ≤ M) :
    lap (odo 1 (2 * M) (fun _ => 2) t) (radial 1 0)
      = odo 1 (2 * M) (fun _ => 2) t (radial 1 1)
        - odo 1 (2 * M) (fun _ => 2) t (radial 1 0) := by
  have hzero : odo 1 (2 * M) (fun _ => 2) t (fun _ => (0 : ℤ))
      = odo 1 (2 * M) (fun _ => 2) t (radial 1 0) := by
    have h := odo_reflect_d1 M t (fun _ => (0 : ℤ))
    have e : (fun i : Fin 1 => 1 - (fun _ => (0 : ℤ)) i) = radial 1 0 := by
      funext i; simp [radial]
    rw [e] at h
    exact h.symm
  have hadd : radial 1 0 + unit (0 : Fin 1) = radial 1 1 := by
    funext i
    simp only [Pi.add_apply, radial, unit, Pi.single_apply, Fin.ext_iff]
    norm_num
  have hsub : radial 1 0 - unit (0 : Fin 1) = fun _ => (0 : ℤ) := by
    funext i
    simp only [Pi.sub_apply, radial, unit, Pi.single_apply, Fin.ext_iff]
    norm_num
  rw [lap, nbrSum, Fin.sum_univ_one, hadd, hsub, hzero]
  ring

/-- The radial site `(2_k, 1_{d-k})` lies in the hypercube `C_N^{(d)}` whenever
`N ≥ 4` and `k ≤ d`. -/
theorem inCube_radial_of_le (d N k : ℕ) (hN : 4 ≤ N) (_hk : k ≤ d) :
    inCube d N (radial d k) := by
  intro i
  rw [loCoord, hiCoord, sideHalf, radial]
  split_ifs <;> omega



open LatticeProb

theorem weak_facet_d1 (M t : ℕ) (hM : 2 ≤ M) (_ht : 1 ≤ t)
    (h : odoUnif 1 (2 * M) t (radial 1 0) = odoUnif 1 (2 * M) t (radial 1 1) + 1) :
    odoUnif 1 (2 * M) (t + 1) (radial 1 0) = odoUnif 1 (2 * M) t (radial 1 0) := by
  have hc : odo 1 (2 * M) (fun _ => 2) t (radial 1 0)
      = odo 1 (2 * M) (fun _ => 2) t (radial 1 1) + 1 := h
  simp only [odoUnif, Nat.cast_one, mul_one]
  rw [odo_succ_eq 1 (2 * M) (fun _ => 2) t (radial 1 0)
    (inCube_radial_of_le 1 (2 * M) 0 (by omega) (by omega))]
  rw [if_neg]
  · ring
  · rw [sandp, lap_radial_d1 M t hM]
    omega

end DimRed
