/-
Monotonicity of the odometer in time, and the terminal odometer `v_∞` when the
process has stabilized.
-/
import DimRed.Support.Recursion

namespace DimRed

open LatticeProb

theorem odo_nonneg (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ odo d N s₀ t x := by
  induction t with
  | zero => exact le_refl 0
  | succ n ih => have h := (odo_succ_sub_bounds d N s₀ n x).1; linarith

theorem odo_mono (d N : ℕ) (s₀ : Site d → ℤ) {m n : ℕ} (h : m ≤ n) (x : Site d) :
    odo d N s₀ m x ≤ odo d N s₀ n x := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · exact le_trans (ih (Nat.lt_succ_iff.mp hm)) (by
        have := (odo_succ_sub_bounds d N s₀ k x).1; linarith)
    · have : m = k + 1 := le_antisymm h hm
      subst this; exact le_rfl

theorem odo_succ_fun (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) :
    odo d N s₀ (t + 1) = fun x => if inCube d N x then
      odo d N s₀ t x + (if 2 * (d : ℤ) ≤ s₀ x + lap (odo d N s₀ t) x then 1 else 0)
      else 0 := rfl

theorem odo_const_of_stable (d N : ℕ) (s₀ : Site d → ℤ) (T : ℕ)
    (h : odo d N s₀ (T + 1) = odo d N s₀ T) :
    ∀ n : ℕ, odo d N s₀ (T + n) = odo d N s₀ T := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    have e : T + (k + 1) = (T + k) + 1 := by omega
    rw [e, odo_succ_fun, ih, ← odo_succ_fun, h]

theorem odoInf_eq_of_stable (d N : ℕ) (s₀ : Site d → ℤ) (T : ℕ)
    (h : odo d N s₀ (T + 1) = odo d N s₀ T) (x : Site d) :
    odoInf d N s₀ x = ((odo d N s₀ T x).toNat : ℕ∞) := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    have hle : odo d N s₀ t x ≤ odo d N s₀ T x := by
      rcases Nat.le_total t T with ht | ht
      · exact odo_mono d N s₀ ht x
      · have := odo_const_of_stable d N s₀ T h (t - T)
        have ht' : T + (t - T) = t := by omega
        rw [ht'] at this
        exact le_of_eq (congrFun this x)
    exact_mod_cast Int.toNat_le_toNat hle
  · exact le_iSup (fun t : ℕ => ((odo d N s₀ t x).toNat : ℕ∞)) T

end DimRed
