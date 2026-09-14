/-
The elementary properties of the block edge `a_t` of `dimred.tex:784-790`:
it is nonincreasing in `t`.
-/
import DimRed.Support.Radial

namespace DimRed

open LatticeProb


theorem tCrit_le_one {d : ℕ} (hd : d ≤ 1) : tCrit d ≤ 1 := by
  have : d - 1 = 0 := by omega
  simp [tCrit, ceilSqrt, this]

theorem ediv_anti (a : ℤ) (ha : 0 ≤ a) (b c : ℤ) (hb : 0 < b) (hbc : b ≤ c) :
    a / c ≤ a / b := by
  rw [Int.le_ediv_iff_mul_le hb]
  have h3 : a / c * b ≤ a / c * c := by
    apply Int.mul_le_mul_of_nonneg_left hbc
    exact Int.ediv_nonneg ha (by omega)
  have h4 : a / c * c ≤ a := Int.ediv_mul_le a (by omega)
  linarith

theorem blockEdge_antitone (d t : ℕ) : blockEdge d (t + 1) ≤ blockEdge d t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t with
    | 0 => exact le_rfl
    | 1 =>
      have h1 : blockEdge d 1 = (d : ℤ) := rfl
      have h2 : blockEdge d 2 = if 2 ≤ tCrit d then ((d : ℤ) - 1) / 1 else blockEdge d 1 - 1 := rfl
      rw [h1, h2]
      split_ifs with h
      · have hd : 2 ≤ d := by
          by_contra hc
          have := tCrit_le_one (by omega : d ≤ 1)
          omega
        have := Int.ediv_le_self ((d : ℤ) - 1) (by omega : (0:ℤ) ≤ (d:ℤ) - 1)
        omega
      · omega
    | (n + 2) =>
      have h1 : blockEdge d (n + 3) = if n + 3 ≤ tCrit d then ((d : ℤ) - 1) / ((n : ℤ) + 2) else blockEdge d (n + 2) - 1 := rfl
      have h2 : blockEdge d (n + 2) = if n + 2 ≤ tCrit d then ((d : ℤ) - 1) / ((n : ℤ) + 1) else blockEdge d (n + 1) - 1 := rfl
      rw [h1, h2]
      split_ifs with h1' h2'
      · have hd : 2 ≤ d := by
          by_contra hc
          have := tCrit_le_one (by omega : d ≤ 1)
          omega
        exact ediv_anti ((d:ℤ)-1) (by omega) ((n:ℤ)+1) ((n:ℤ)+2) (by omega) (by omega)
      · omega
      · omega
      · have := ih (n + 1) (by omega)
        omega


theorem tCrit_pos (d : ℕ) : 1 ≤ tCrit d := by
  rw [tCrit, ceilSqrt]
  split <;> omega

theorem tCrit_sq (d : ℕ) : d - 1 ≤ tCrit d * tCrit d := by
  rcases d with _ | _ | d
  · norm_num [tCrit, ceilSqrt]
  · norm_num [tCrit, ceilSqrt]
  · have h : d < (d.sqrt + 1) * (d.sqrt + 1) := Nat.lt_succ_sqrt d
    have hc : tCrit (d + 2) = d.sqrt + 2 := by rw [tCrit, ceilSqrt]; norm_num
    rw [hc]
    have hz : (0:ℤ) ≤ (d.sqrt : ℤ) := by omega
    have h' : (d : ℤ) < ((d.sqrt : ℤ) + 1) * ((d.sqrt : ℤ) + 1) := by exact_mod_cast h
    have hgoal : (d + 1 : ℕ) ≤ (d.sqrt + 2) * (d.sqrt + 2) := by
      have h'' : d + 1 ≤ (d.sqrt + 1) * (d.sqrt + 1) := by omega
      nlinarith [h'', Nat.zero_le d.sqrt]
    simpa using hgoal

theorem blockEdge_of_le (d m : ℕ) (hm : 2 ≤ m) (h : m ≤ tCrit d) :
    blockEdge d m = ((d : ℤ) - 1) / ((m : ℤ) - 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => omega
    | (n + 2) =>
      rw [blockEdge]
      rw [if_pos (by omega : n + 2 ≤ tCrit d)]
      have hcast : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]

theorem blockEdge_of_gt (d m : ℕ) (hm : tCrit d < m) :
    blockEdge d m = blockEdge d (tCrit d) - ((m : ℤ) - (tCrit d : ℤ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => exact absurd hm (by have := tCrit_pos d; omega)
    | (n + 2) =>
      rw [blockEdge]
      rw [if_neg (by omega : ¬ n + 2 ≤ tCrit d)]
      rcases Nat.eq_or_lt_of_le (by omega : tCrit d ≤ n + 1) with he | hlt
      · have he' : n + 1 = tCrit d := he.symm
        have hcast : ((n + 2 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ) = 1 := by
          have : ((tCrit d : ℕ) : ℤ) = (n : ℤ) + 1 := by rw [he]; push_cast; ring
          rw [this]; push_cast; ring
        rw [hcast]
        have : n + 1 = tCrit d := he'
        rw [← this]
      · have hh := ih (n + 1) (by omega) hlt
        rw [hh]
        have hcast : ((n + 2 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ)
            = ((n + 1 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ) + 1 := by push_cast; ring
        rw [hcast]
        ring


theorem tCrit_eq (d : ℕ) (hd : 2 ≤ d) : tCrit d = (d - 2).sqrt + 2 := by
  rw [tCrit, ceilSqrt]
  rw [if_neg (by omega : ¬ (d - 1 = 0))]
  have h : d - 1 - 1 = d - 2 := by omega
  rw [h]

theorem tCrit_sub_one_sq (d : ℕ) (hd : 2 ≤ d) : d - 1 ≤ (tCrit d - 1) * (tCrit d - 1) := by
  rw [tCrit_eq d hd]
  have h : (d - 2).sqrt + 2 - 1 = (d - 2).sqrt + 1 := by omega
  rw [h]
  have h1 : d - 2 < ((d - 2).sqrt + 1) * ((d - 2).sqrt + 1) := Nat.lt_succ_sqrt _
  have h2 : d - 1 ≤ ((d - 2).sqrt + 1) * ((d - 2).sqrt + 1) := by omega
  exact_mod_cast h2

theorem tCrit_sub_one_pos (d : ℕ) (hd : 2 ≤ d) : 1 ≤ tCrit d - 1 := by
  rw [tCrit_eq d hd]; omega

theorem ediv_le_succ (d : ℕ) (hd : 2 ≤ d) : ((d : ℤ) - 1) / ((tCrit d - 1 : ℕ) : ℤ) ≤ (tCrit d - 1 : ℕ) := by
  set s : ℕ := tCrit d - 1 with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact tCrit_sub_one_pos d hd
  have hsq : d - 1 ≤ s * s := by rw [hsdef]; exact tCrit_sub_one_sq d hd
  have hspos : (0:ℤ) < (s:ℤ) := by omega
  have hsqz : ((d : ℤ) - 1) ≤ (s:ℤ) * (s:ℤ) := by
    have hc2 : ((s * s : ℕ) : ℤ) = (s:ℤ) * (s:ℤ) := by push_cast; ring
    have hc3 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    rw [← hc2, ← hc3]
    exact_mod_cast hsq
  have hlt : ((d : ℤ) - 1) / (s : ℤ) < (s : ℤ) + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hspos]
    nlinarith [hsqz, hspos]
  linarith

theorem blockEdge_mul_le (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    blockEdge d (t + 1) * (t : ℤ) ≤ (d : ℤ) - 1 := by
  by_cases h : t + 1 ≤ tCrit d
  · rw [blockEdge_of_le d (t + 1) (by omega) h]
    have hcast : (((t + 1 : ℕ) : ℤ) - 1) = (t : ℤ) := by push_cast; ring
    rw [hcast]
    exact Int.ediv_mul_le _ (by omega)
  · have htc : tCrit d ≤ t := by omega
    by_cases hd1 : d = 1
    · subst hd1
      have htc1 : tCrit 1 = 1 := by rw [tCrit, ceilSqrt]; norm_num
      rw [blockEdge_of_gt 1 (t + 1) (by rw [htc1]; omega)]
      rw [htc1]
      have hb1 : blockEdge 1 1 = (1 : ℤ) := by rw [blockEdge]; norm_num
      rw [hb1]
      have hstep : ((t + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = (t : ℤ) := by push_cast; ring
      rw [hstep]
      have ht0 : (1:ℤ) ≤ (t:ℤ) := by omega
      have h2 : (0:ℤ) ≤ (t:ℤ) := by linarith
      have hmul : (1 - (t:ℤ)) * (t:ℤ) ≤ 0 := by nlinarith [ht0, h2]
      simpa using hmul
    have hd2 : 2 ≤ d := by omega
    have hs : 2 ≤ tCrit d := by rw [tCrit_eq d hd2]; omega
    rw [blockEdge_of_gt d (t + 1) (by omega)]
    rw [blockEdge_of_le d (tCrit d) hs le_rfl]
    have hcast : (((tCrit d : ℕ) : ℤ) - 1) = ((tCrit d - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ tCrit d)]; ring
    rw [hcast]
    set s : ℕ := tCrit d - 1 with hsdef
    have hs1 : 1 ≤ s := by rw [hsdef]; omega
    have hspos : (0:ℤ) < (s:ℤ) := by omega
    have hq : ((d : ℤ) - 1) / (s : ℤ) ≤ (s : ℤ) := by
      have h := ediv_le_succ d hd2
      rw [← hsdef] at h
      exact h
    have hqs : ((d : ℤ) - 1) / (s : ℤ) * (s : ℤ) ≤ (d : ℤ) - 1 :=
      Int.ediv_mul_le _ (by omega)
    have htge : (s : ℤ) + 1 ≤ (t : ℤ) := by
      have h2 : tCrit d ≤ t := htc
      have h3 : ((tCrit d : ℕ) : ℤ) ≤ (t : ℤ) := by exact_mod_cast h2
      have h4 : ((tCrit d - 1 : ℕ) : ℤ) = (tCrit d : ℤ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ tCrit d)]; ring
      rw [hsdef, h4]
      linarith
    have hstep : ((t + 1 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ) = (t : ℤ) - (s : ℤ) := by
      rw [hsdef]; push_cast [Nat.cast_sub (by omega : 1 ≤ tCrit d)]; ring
    rw [hstep]
    set q : ℤ := ((d : ℤ) - 1) / (s : ℤ) with hqdef
    have hqle : q ≤ (s : ℤ) := hq
    have hqmul : q * (s : ℤ) ≤ (d : ℤ) - 1 := hqs
    have hkey : (q - ((t : ℤ) - (s : ℤ))) * (t : ℤ) ≤ q * (s : ℤ) := by
      have hu : 1 ≤ (t : ℤ) - (s : ℤ) := by linarith
      have htq : (s : ℤ) ≤ (t : ℤ) := by linarith
      nlinarith [hu, htq, hqle]
    linarith

/-- The sandpile on the block, `dimred.tex:821-826`: if the odometer is `t` at
the radial sites `x-1`, `x`, `x+1`, then the sandpile at `x` is
`2d + (d-1) - t x`. -/
theorem sandp_block (d t : ℕ) (_hd : 1 ≤ d) (_ht : 1 ≤ t) (x : ℕ) (hx : x ≤ d)
    (h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (t : ℤ))
    (h1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1)) = (t : ℤ))
    (hm : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = (t : ℤ)) :
    sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)
      = 2 * (d : ℤ) + ((d : ℤ) - 1) - (t : ℤ) * (x : ℤ) := by
  rw [sandp, lap_radial d (2 * (d:ℤ) + ((d:ℤ) - 1)) t x hx, h0, h1, hm]; ring
