/-
The radial reparameterization of `S_2^{(d)}`, `dimred.tex:722-733`: the
hypercube of side `4`, the points `(2_k, 1_{d-k})`, and how the neighbours of
such a point are carried back to the radial family by a symmetry of the cube.
The last theorem is the Laplacian of Lemma 3.1.
-/
import DimRed.Support.CubeTwo

namespace DimRed

open LatticeProb

theorem loCoord_four : loCoord 4 = -1 := by norm_num [loCoord]

theorem hiCoord_four : hiCoord 4 = 2 := by norm_num [hiCoord, sideHalf]

theorem unit_apply' (d : ℕ) (i j : Fin d) :
    (unit i : Site d) j = if (j : ℕ) = (i : ℕ) then 1 else 0 := by
  simp [unit, Pi.single_apply, Fin.ext_iff]

theorem odo_comp_perm (d N : ℕ) (s₀ : Site d → ℤ) (hsym : IsSymmetricPile d N s₀)
    (t : ℕ) (π : Equiv.Perm (Fin d)) (y : Site d) :
    odo d N s₀ t (fun j => y (π j)) = odo d N s₀ t y := by
  have h := odo_cubeSym d N s₀ hsym t π (fun _ => true) y
  have e : cubeSym d N π (fun _ => true) y = fun j => y (π j) := by
    funext j; simp [cubeSym]
  rwa [e] at h

theorem radial_apply (d k : ℕ) (j : Fin d) :
    radial d k j = if (j : ℕ) < k then 2 else 1 := rfl

theorem radial_sub_unit_lt (d k : ℕ) (i : Fin d) (hi : (i : ℕ) < k) (hb : k - 1 < d) :
    radial d k - unit i = fun j => radial d (k - 1) (Equiv.swap i ⟨k - 1, hb⟩ j) := by
  funext j
  have hval : ((⟨k - 1, hb⟩ : Fin d) : ℕ) = k - 1 := rfl
  by_cases hji : j = i
  · subst hji
    rw [Equiv.swap_apply_left]
    simp only [Pi.sub_apply, radial_apply, unit_apply']
    split_ifs <;> omega
  · by_cases hjb : j = (⟨k - 1, hb⟩ : Fin d)
    · subst hjb
      rw [Equiv.swap_apply_right]
      have hne : ((⟨k - 1, hb⟩ : Fin d) : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
      simp only [Pi.sub_apply, radial_apply, unit_apply'] at hne ⊢
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne hji hjb]
      have hne1 : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
      have hne2 : (j : ℕ) ≠ k - 1 := fun h => hjb (Fin.ext (by rw [hval]; exact h))
      simp only [Pi.sub_apply, radial_apply, unit_apply']
      split_ifs <;> omega

theorem radial_add_unit_ge (d k : ℕ) (i : Fin d) (hi : k ≤ (i : ℕ)) (hb : k < d) :
    radial d k + unit i = fun j => radial d (k + 1) (Equiv.swap i ⟨k, hb⟩ j) := by
  funext j
  have hval : ((⟨k, hb⟩ : Fin d) : ℕ) = k := rfl
  by_cases hji : j = i
  · subst hji
    rw [Equiv.swap_apply_left]
    simp only [Pi.add_apply, radial_apply, unit_apply']
    split_ifs <;> omega
  · by_cases hjb : j = (⟨k, hb⟩ : Fin d)
    · subst hjb
      rw [Equiv.swap_apply_right]
      have hne : ((⟨k, hb⟩ : Fin d) : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
      simp only [Pi.add_apply, radial_apply, unit_apply'] at hne ⊢
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne hji hjb]
      have hne1 : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
      have hne2 : (j : ℕ) ≠ k := fun h => hjb (Fin.ext (by rw [hval]; exact h))
      simp only [Pi.add_apply, radial_apply, unit_apply']
      split_ifs <;> omega

theorem radial_sub_unit_ge (d k : ℕ) (i : Fin d) (hi : k ≤ (i : ℕ)) :
    radial d k - unit i
      = cubeSym d 4 (Equiv.refl (Fin d)) (fun j => decide (j ≠ i)) (radial d k) := by
  funext j
  simp only [cubeSym, Equiv.refl_apply, loCoord_four, hiCoord_four, decide_eq_true_eq,
    Pi.sub_apply, radial_apply, unit_apply']
  by_cases hji : j = i
  · subst hji
    simp only [if_neg (by simp : ¬ (j ≠ j))]
    split_ifs <;> omega
  · have hne1 : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
    simp only [if_pos hji]
    split_ifs <;> omega

theorem radial_add_unit_out (d k : ℕ) (i : Fin d) (hi : (i : ℕ) < k) :
    ¬ inCube d 4 (radial d k + unit i) := by
  intro h
  have h2 := (h i).2
  rw [hiCoord_four, Pi.add_apply, radial_apply, unit_apply', if_pos rfl, if_pos hi] at h2
  omega

theorem isSymmetricPile_const (d N : ℕ) (c : ℤ) : IsSymmetricPile d N (fun _ => c) :=
  fun _ _ _ => rfl

theorem nbrSum_radial (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    nbrSum (odo d 4 (fun _ => c) t) (radial d k)
      = (k : ℤ) * odo d 4 (fun _ => c) t (radial d (k - 1))
        + ((d : ℤ) - (k : ℤ)) * (odo d 4 (fun _ => c) t (radial d (k + 1))
            + odo d 4 (fun _ => c) t (radial d k)) := by
  have hsym := isSymmetricPile_const d 4 c
  set v : Site d → ℤ := odo d 4 (fun _ => c) t with hv
  have key : ∀ i : Fin d, (v (radial d k + unit i) + v (radial d k - unit i))
      = if (i : ℕ) < k then v (radial d (k - 1))
        else (v (radial d (k + 1)) + v (radial d k)) := by
    intro i
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi]
      have hout := radial_add_unit_out d k i hi
      have hb : k - 1 < d := by omega
      rw [hv, odo_eq_zero_outside d 4 (fun _ => c) t _ hout,
        radial_sub_unit_lt d k i hi hb, odo_comp_perm d 4 (fun _ => c) hsym t _ _]
      ring
    · rw [if_neg hi]
      rw [not_lt] at hi
      have hb : k < d := by omega
      rw [hv, radial_add_unit_ge d k i hi hb, odo_comp_perm d 4 (fun _ => c) hsym t _ _,
        radial_sub_unit_ge d k i hi, odo_cubeSym d 4 (fun _ => c) hsym t _ _]
  simp only [nbrSum, key]
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < k then v (radial d (k - 1))
    else (v (radial d (k + 1)) + v (radial d k))) d]
  rw [Finset.sum_ite]
  have e1 : (Finset.range d).filter (fun m => m < k) = Finset.range k := by
    ext m; simp; omega
  have e2 : ((Finset.range d).filter (fun m => ¬ m < k)).card = d - k := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.range d) (p := fun m => m < k)
    rw [e1, Finset.card_range, Finset.card_range] at h
    omega
  rw [Finset.sum_const, Finset.sum_const, e1, Finset.card_range, e2]
  simp only [nsmul_eq_mul]
  push_cast [Nat.cast_sub hk]
  ring

theorem lap_radial (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    lap (odo d 4 (fun _ => c) t) (radial d k)
      = (-(d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d k)
        + ((d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d (k + 1))
        + (k : ℤ) * odo d 4 (fun _ => c) t (radial d (k - 1)) := by
  rw [lap, nbrSum_radial d c t k hk]
  ring

theorem inCube_radial (d k : ℕ) : inCube d 4 (radial d k) := by
  intro i
  rw [loCoord_four, hiCoord_four, radial_apply]
  split <;> omega

theorem odo_radial_succ (d : ℕ) (c : ℤ) (t k : ℕ) (hk : k ≤ d) :
    odo d 4 (fun _ => c) (t + 1) (radial d k)
      = odo d 4 (fun _ => c) t (radial d k)
        + (if 2 * (d : ℤ) ≤ c
              + ((-(d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d k)
                + ((d : ℤ) - (k : ℤ)) * odo d 4 (fun _ => c) t (radial d (k + 1))
                + (k : ℤ) * odo d 4 (fun _ => c) t (radial d (k - 1)))
            then 1 else 0) := by
  rw [odo_succ_eq d 4 (fun _ => c) t (radial d k) (inCube_radial d k)]
  simp only [sandp, lap_radial d c t k hk]

end DimRed
