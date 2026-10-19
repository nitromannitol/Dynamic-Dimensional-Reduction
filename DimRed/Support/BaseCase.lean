/-
The elementary properties of the block edge `a_t` of `dimred-corrected-arxiv.tex:655-661`:
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

/-- The sandpile on the block, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`: if the odometer is `t` at
the radial sites `x-1`, `x`, `x+1`, then the sandpile at `x` is
`2d + (d-1) - t x`. -/
theorem sandp_block (d t : ℕ) (_hd : 1 ≤ d) (_ht : 1 ≤ t) (x : ℕ) (hx : x ≤ d)
    (h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (t : ℤ))
    (h1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1)) = (t : ℤ))
    (hm : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = (t : ℤ)) :
    sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)
      = 2 * (d : ℤ) + ((d : ℤ) - 1) - (t : ℤ) * (x : ℤ) := by
  rw [sandp, lap_radial d (2 * (d:ℤ) + ((d:ℤ) - 1)) t x hx, h0, h1, hm]; ring

/-- Inside the firing block at time `t + 1` the excess `(d-1) - t x` is
nonnegative, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem blockEdge_window_le (d t x : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) (_hx : x ≤ d)
    (h : (x : ℤ) ≤ blockEdge d (t + 1)) : (x : ℤ) * (t : ℤ) ≤ (d : ℤ) - 1 := by
  have h1 : (x : ℤ) * (t : ℤ) ≤ blockEdge d (t + 1) * (t : ℤ) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h2 := blockEdge_mul_le d t hd ht
  linarith

/-- The strict decrease of `a / m` in `m` when `a ≥ m²`. -/
theorem ediv_strict_succ (a : ℤ) (t : ℕ) (ht : 1 ≤ t) (h : (t : ℤ) * (t : ℤ) ≤ a) :
    a / ((t : ℤ) + 1) < a / (t : ℤ) := by
  have ht_pos : (0 : ℤ) < (t : ℤ) := by omega
  have ht1_pos : (0 : ℤ) < (t : ℤ) + 1 := by omega
  have hq : (t : ℤ) ≤ a / (t : ℤ) := by
    rw [Int.le_ediv_iff_mul_le ht_pos]
    exact h
  have hlt : a < (a / (t : ℤ) + 1) * (t : ℤ) := by
    rw [← Int.ediv_lt_iff_lt_mul ht_pos]
    omega
  have key : a < (a / (t : ℤ)) * ((t : ℤ) + 1) := by
    nlinarith [hq, hlt]
  rw [Int.ediv_lt_iff_lt_mul ht1_pos]
  exact key

/-- The block edge strictly decreases, `dimred-corrected-arxiv.tex:655-661`. -/
theorem blockEdge_strict (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    blockEdge d (t + 1) < blockEdge d t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  match u with
  | 0 =>
    have h1 : blockEdge d 1 = (d : ℤ) := rfl
    have h2 : blockEdge d 2 = if 2 ≤ tCrit d then ((d : ℤ) - 1) / 1 else blockEdge d 1 - 1 := rfl
    rw [h1, h2]
    split_ifs with h
    · have hd2 : 2 ≤ d := by
        by_contra hcc
        have h2 : tCrit d ≤ 1 := tCrit_le_one (by omega : d ≤ 1)
        omega
      have hq : ((d : ℤ) - 1) / 1 = (d : ℤ) - 1 := by norm_num
      rw [hq]; omega
    · omega
  | (n + 1) =>
    by_cases hc : n + 2 + 1 ≤ tCrit d
    · have htc : n + 2 ≤ tCrit d := by omega
      rw [blockEdge_of_le d (n + 2 + 1) (by omega) hc, blockEdge_of_le d (n + 2) (by omega) htc]
      have hcast1 : (((n + 2 + 1 : ℕ) : ℤ) - 1) = ((n : ℤ) + 2) := by push_cast; ring
      have hcast2 : (((n + 2 : ℕ) : ℤ) - 1) = ((n : ℤ) + 1) := by push_cast; ring
      rw [hcast1, hcast2]
      have hd2 : 2 ≤ d := by
        by_contra hcc
        have h2 : tCrit d ≤ 1 := tCrit_le_one (by omega : d ≤ 1)
        omega
      have hsq : ((n : ℤ) + 1) * ((n : ℤ) + 1) ≤ (d : ℤ) - 1 := by
        have h3 : tCrit d = (d - 2).sqrt + 2 := tCrit_eq d hd2
        have h4 : n + 1 ≤ (d - 2).sqrt := by omega
        have h5 : (n + 1) * (n + 1) ≤ (d - 2).sqrt * (d - 2).sqrt := by
          nlinarith [h4, Nat.zero_le n]
        have h6 : (d - 2).sqrt * (d - 2).sqrt ≤ d - 2 := Nat.sqrt_le _
        have h7 : (n + 1) * (n + 1) ≤ d - 2 := le_trans h5 h6
        have h8 : (n + 1) * (n + 1) ≤ d - 1 := by omega
        exact_mod_cast h8
      have hstep := ediv_strict_succ ((d : ℤ) - 1) (n + 1) (by omega) hsq
      have hcast3 : ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 2) := by push_cast; ring
      rwa [hcast3] at hstep
    · have hle : tCrit d ≤ n + 1 + 1 := by omega
      by_cases hlt : tCrit d < n + 1 + 1
      · rw [blockEdge_of_gt d (n + 1 + 1 + 1) (by omega), blockEdge_of_gt d (n + 1 + 1) hlt]
        have hcast : ((n + 1 + 1 + 1 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ)
            = ((n + 1 + 1 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ) + 1 := by push_cast; ring
        rw [hcast]; omega
      · have heq : tCrit d = n + 1 + 1 := by omega
        rw [blockEdge_of_gt d (n + 1 + 1 + 1) (by omega)]
        have hcast : ((n + 1 + 1 + 1 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ) = 1 := by
          rw [heq]; push_cast; ring
        rw [hcast, heq]; omega

/-- The block clause of the base case from the invariant at times `t` and `t+1`. -/
theorem base_block_from_inv (d : ℕ) (_hd : 1 ≤ d) (t : ℕ)
    (h1 : ∀ x : ℕ, x ≤ d → (x : ℤ) ≤ blockEdge d (t + 1) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x) = ((t + 1 : ℕ) : ℤ))
    (h2 : ∀ x : ℕ, 1 ≤ x → x ≤ d → blockEdge d (t + 1) < (x : ℤ) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)))
    (h3 : ∀ x : ℕ, x ≤ d → (x : ℤ) ≤ blockEdge d t →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (t : ℤ))
    (h4 : blockEdge d (t + 1) < 0 →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d 0) = (t : ℤ)) :
    ∀ x : ℕ, x ≤ d →
      ((x : ℤ) ≤ blockEdge d (t + 1) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) + 1) ∧
      (blockEdge d (t + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d t →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)) := by
  intro x hx
  constructor
  · intro h
    have hA := h1 x hx h
    have hB := h3 x hx (le_trans h (blockEdge_antitone d t))
    push_cast at hA
    omega
  · intro h1' h2'
    by_cases hx1 : 1 ≤ x
    · have hA := h2 x hx1 hx h1'
      have hB := h3 (x - 1) (by omega) (by omega)
      have hC := h3 x hx h2'
      omega
    · have h0 : x = 0 := by omega
      subst h0
      have hA := h4 h1'
      have hB := h3 0 hx h2'
      omega

/-- `a_t` is nonincreasing in `t`. -/
theorem blockEdge_antitone_le (d : ℕ) {m n : ℕ} (h : m ≤ n) : blockEdge d n ≤ blockEdge d m := by
  induction h with
  | refl => exact le_rfl
  | step hk ih => exact le_trans (blockEdge_antitone d _) ih

/-- The excess bound read at the front `s`: `x ≤ a_s` gives
`x (s-1) ≤ d-1`, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem blockEdge_window_le' (d s x : ℕ) (hd : 1 ≤ d) (_hx : x ≤ d)
    (h : (x : ℤ) ≤ blockEdge d s) : (x : ℤ) * ((s : ℤ) - 1) ≤ (d : ℤ) - 1 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp only [blockEdge] at h
    push_cast
    nlinarith [h]
  · have hs : 1 ≤ s := by omega
    by_cases hs1 : s = 1
    · subst hs1
      simp only [blockEdge] at h
      push_cast
      nlinarith [h]
    · have hs2 : 2 ≤ s := by omega
      have hm := blockEdge_mul_le d (s - 1) hd (by omega)
      have hcast : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by push_cast [Nat.cast_sub hs]; ring
      have hsub : s - 1 + 1 = s := by omega
      rw [hsub, hcast] at hm
      nlinarith [h, hm]

/-- The paper's first displayed chain of Step 2, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`: if the
odometer at time `t` is `s+1` at `x-1` and `s` at `x` and `x+1`, then the
sandpile at `x` is at least `2d`. -/
theorem sandp_ge_two_d (d t s x : ℕ) (hd : 1 ≤ d) (_hs : s + 1 ≤ t) (_hx : t - s ≤ x) (hxd : x ≤ d)
    (hxs : (x : ℤ) ≤ blockEdge d s)
    (h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = ((s + 1 : ℕ) : ℤ))
    (h1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (s : ℤ))
    (h2 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1)) = (s : ℤ)) :
    2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
  have hcast : ((s + 1 : ℕ) : ℤ) = (s : ℤ) + 1 := by push_cast; ring
  have h0' : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = (s : ℤ) + 1 := by
    rw [h0, hcast]
  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) t x hxd, h1, h2, h0']
  have hw : (x : ℤ) * ((s : ℤ) - 1) ≤ (d : ℤ) - 1 :=
    blockEdge_window_le' d s x hd hxd hxs
  nlinarith [hw]

/-- The sandpile at a site of the firing block is at least `2d`, so the site
fires, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem sandp_block_ge (d n x : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hx : x ≤ d)
    (h1 : (x : ℤ) ≤ blockEdge d (n + 1))
    (hAn : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d x) = (n : ℤ))
    (hA1 : (x + 1 : ℤ) ≤ blockEdge d n →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d (x + 1)) = (n : ℤ))
    (hA0 : (x - 1 : ℤ) ≤ blockEdge d n →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d (x - 1)) = (n : ℤ)) :
    2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d x) := by
  have hlt : blockEdge d (n + 1) < blockEdge d n := blockEdge_strict d n hd hn
  have hle : blockEdge d (n + 1) ≤ blockEdge d n := le_of_lt hlt
  rw [sandp, lap_radial d _ n x hx, hAn]
  have h1' : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d (x - 1)) = (n : ℤ) :=
    hA0 (by omega)
  rw [h1']
  by_cases hxd : x = d
  · rw [hxd]
    simp only [sub_self, zero_mul, add_zero]
    have hw := blockEdge_window_le d n x hd hn hx h1
    nlinarith [hw]
  · have h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) n (radial d (x + 1)) = (n : ℤ) :=
      hA1 (by omega)
    rw [h0]
    have hw := blockEdge_window_le d n x hd hn hx h1
    nlinarith [hw]

/-- The block edge never exceeds `d`, `dimred-corrected-arxiv.tex:655-661`. -/
theorem blockEdge_le_self (d m : ℕ) (hd : 1 ≤ d) : blockEdge d m ≤ (d : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp only [blockEdge]; exact le_rfl
    | 1 => simp only [blockEdge]; exact le_rfl
    | (n + 2) =>
      by_cases h : n + 2 ≤ tCrit d
      · rw [blockEdge_of_le d (n + 2) (by omega) h]
        have hcast : (((n + 2 : ℕ) : ℤ) - 1) = (n : ℤ) + 1 := by push_cast; ring
        rw [hcast]
        have hpos : (0 : ℤ) < (n : ℤ) + 1 := by omega
        have hle : ((d : ℤ) - 1) / ((n : ℤ) + 1) ≤ (d : ℤ) - 1 :=
          Int.ediv_le_self _ (by omega)
        linarith
      · rw [blockEdge_of_gt d (n + 2) (by omega)]
        have htc : tCrit d ≤ n + 1 := by omega
        have hb : blockEdge d (tCrit d) ≤ (d : ℤ) := ih (tCrit d) (by omega)
        have hcast : (((n + 2 : ℕ) : ℤ) - ((tCrit d : ℕ) : ℤ)) = (n : ℤ) + 2 - (tCrit d : ℤ) := by
          push_cast; ring
        rw [hcast]
        have h1 : (tCrit d : ℤ) ≤ (n : ℤ) + 1 := by omega
        linarith

/-- The ripple step when the site fires: `v_{t+1}(x) = v_t(x-1)` follows from
`odo_succ_eq` and the hypothesis `v_t(x-1) = v_t(x) + 1`, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem ripple_step_ge (d t x : ℕ) (_hd : 1 ≤ d) (_hx : x ≤ d)
    (h : 2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x))
    (hx1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1))
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) + 1) :
    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) := by
  rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) (inCube_radial d x)]
  rw [if_pos h]
  omega

/-- The ripple step when the site does not fire: `v_{t+1}(x) = v_t(x-1)` follows
from `odo_succ_eq` and the hypothesis `v_t(x-1) = v_t(x)`, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem ripple_step_lt (d t x : ℕ) (_hd : 1 ≤ d) (_hx : x ≤ d)
    (h : ¬ 2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x))
    (hx1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1))
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)) :
    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) := by
  rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) (inCube_radial d x)]
  rw [if_neg h]
  omega

/-- The ripple step, split on whether the site fires, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem ripple_window_step (d t x : ℕ) (_hd : 1 ≤ d) (_hx : x ≤ d)
    (hge : 2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1))
        = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) + 1)
    (hlt : ¬ 2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1))
        = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)) :
    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
      = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) := by
  rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) (inCube_radial d x)]
  by_cases h : 2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The paper's first displayed chain of Step 2, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`: if the
odometer at time `t` is `s` at `x-2` and `x-1` and `s-1` at `x` and `x+1`, and
`x ≤ a_s`, then the sandpile at `x` is at least `2d`. -/
theorem sandp_ge_two_d' (d t s x : ℕ) (hd : 1 ≤ d) (hx : x ≤ d) (h2 : 2 ≤ x)
    (hxs : (x : ℤ) ≤ blockEdge d s)
    (_h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 2)) = (s : ℤ))
    (h1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = (s : ℤ))
    (h2' : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (s : ℤ) - 1)
    (h3 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1)) = (s : ℤ) - 1) :
    2 * (d : ℤ) ≤ sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) t x hx, h2', h3, h1]
  have hw := blockEdge_window_le' d s x hd hx hxs
  nlinarith [hw]

/-- The cast of the shifted index: `x ≤ a + (t - s)` with `t - s ≤ x` gives
`x - (t - s) ≤ a` after casting to `ℤ`. -/
theorem cast_sub_le (d s t x : ℕ) (h : (x : ℤ) ≤ blockEdge d (s + 1) + ((t - s : ℕ) : ℤ))
    (hx : t - s ≤ x) : ((x - (t - s) : ℕ) : ℤ) ≤ blockEdge d (s + 1) := by
  push_cast [Nat.cast_sub hx]
  omega
