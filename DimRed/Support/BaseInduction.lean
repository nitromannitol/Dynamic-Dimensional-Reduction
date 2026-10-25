module

/-
The invariant profile of the parallel toppling odometer for the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`
(Proposition 3.2's proof): the closed value in the firing block (`block_eq`),
the frozen value immediately beyond it (`beyond_block_eq`), and the
front-shifted ripple relation (`ripple_shift`) that together prove
`DimRed.Frozen.base_case`.
-/
public import DimRed.Support.BaseCase
public import DimRed.Support.BaseStep

@[expose] public section

namespace DimRed

open LatticeProb

/-- Floor-division overshoot: `a < (a / b + 1) * b` for `b > 0`. -/
theorem ediv_add_one_mul_gt (a b : ℤ) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h := Int.emod_lt_of_pos a hb
  have he := Int.mul_ediv_add_emod a b
  nlinarith [h, he]

/-- `blockEdge` drops by exactly `1` per step from `tCrit d` onward,
The subsection labelled `subsec:M2` in `dimred-corrected-arxiv.tex`. -/
theorem blockEdge_succ_eq_pred_sub_one (d s : ℕ) (hs : tCrit d ≤ s) :
    blockEdge d (s + 1) = blockEdge d s - 1 := by
  have h1 : blockEdge d (s + 1) = blockEdge d (tCrit d) - (((s + 1 : ℕ) : ℤ) - (tCrit d : ℤ)) :=
    blockEdge_of_gt d (s + 1) (by omega)
  rcases eq_or_lt_of_le hs with heq | hlt
  · have hs' : s = tCrit d := heq.symm
    subst hs'
    rw [h1]; push_cast; ring
  · have h2 : blockEdge d s = blockEdge d (tCrit d) - ((s : ℤ) - (tCrit d : ℤ)) :=
    blockEdge_of_gt d s hlt
    rw [h1, h2]; push_cast; ring

/-- Inside the firing block, the odometer equals the elapsed time,
the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex` (iterating the block clause from `v_1 ≡ 1`). -/
theorem block_eq (d : ℕ) (hd : 1 ≤ d) :
    ∀ T x : ℕ, x ≤ d → (x : ℤ) ≤ blockEdge d T →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) T (radial d x) = (T : ℤ) := by
  intro T
  induction T with
  | zero => intro x _ _; rfl
  | succ n ih =>
    match n with
    | 0 =>
      intro x hx _
      have h1 := odo_radial_one d hd x hx
      have h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) 0 (radial d x) = 0 := rfl
      rw [h0] at h1
      simpa using h1
    | (m + 1) =>
      intro x hx hle
      have hn1 : 1 ≤ m + 1 := by omega
      have hle' : (x : ℤ) ≤ blockEdge d (m + 1) := le_trans hle (blockEdge_antitone d (m + 1))
      have hAn : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (m + 1) (radial d x) = ((m + 1 : ℕ) : ℤ) :=
        ih x hx hle'
      have hA1 : (x + 1 : ℤ) ≤ blockEdge d (m + 1) →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (m + 1) (radial d (x + 1)) = ((m + 1 : ℕ) : ℤ) := by
        intro hxp1
        have hb := blockEdge_le_self d (m + 1) hd
        refine ih (x + 1) (by omega) ?_
        exact_mod_cast hxp1
      have hA0 : (x - 1 : ℤ) ≤ blockEdge d (m + 1) →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (m + 1) (radial d (x - 1)) = ((m + 1 : ℕ) : ℤ) := by
        intro _
        refine ih (x - 1) (by omega) ?_
        have : ((x - 1 : ℕ) : ℤ) ≤ (x : ℤ) := by omega
        omega
      have hfire := sandp_block_ge d (m + 1) x hd hn1 hx hle hAn hA1 hA0
      have hstep := odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (m + 1) (radial d x)
        (inCube_radial d x)
      rw [if_pos hfire] at hstep
      rw [hstep, hAn]
      push_cast; ring

/-- Just beyond the firing block, the odometer stays frozen for one more
step, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`. -/
theorem beyond_block_eq (d : ℕ) (hd : 1 ≤ d) :
    ∀ t x : ℕ, 1 ≤ t → x ≤ d → blockEdge d (t + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d t →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
        = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro x ht hx h1 h2
    have hvx : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (t : ℤ) :=
      block_eq d hd t x hx h2
    have hvxm1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1)) = (t : ℤ) := by
      refine block_eq d hd t (x - 1) (by omega) ?_
      have : ((x - 1 : ℕ) : ℤ) ≤ (x : ℤ) := by omega
      omega
    have hstep := odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x)
      (inCube_radial d x)
    by_cases hxd : x = d
    · have hxd' : (x : ℤ) = (d : ℤ) := by exact_mod_cast hxd
      have hnf : ¬ 2 * (d : ℤ) ≤
          sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
        rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) t x hx, hvx, hvxm1, hxd']
        nlinarith [ht]
      rw [hstep, if_neg hnf, hvx]; ring
    · by_cases hxb : (x : ℤ) = blockEdge d t
      · have hxlt : x < d := by omega
        have ht2 : 2 ≤ t := by
          by_contra hc
          have ht1 : t = 1 := by omega
          subst ht1
          have : blockEdge d 1 = (d : ℤ) := rfl
          rw [this] at hxb
          omega
        have hprev := ih (t - 1) (by omega) (x + 1) (by omega) (by omega)
        have hstrict : blockEdge d t < blockEdge d (t - 1) := by
          have := blockEdge_strict d (t - 1) hd (by omega)
          have he : t - 1 + 1 = t := by omega
          rwa [he] at this
        have hcond1 : blockEdge d (t - 1 + 1) < ((x + 1 : ℕ) : ℤ) := by
          have he : t - 1 + 1 = t := by omega
          rw [he]; push_cast; omega
        have hcond2 : ((x + 1 : ℕ) : ℤ) ≤ blockEdge d (t - 1) := by
          push_cast; omega
        have heq := hprev hcond1 hcond2
        have hblk : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t - 1) (radial d (x + 1))
            = ((t - 1 : ℕ) : ℤ) := block_eq d hd (t - 1) (x + 1) (by omega) hcond2
        have he : t - 1 + 1 = t := by omega
        rw [he] at heq
        have hvxp1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1))
            = (t : ℤ) - 1 := by
          rw [heq, hblk]; omega
        have hnf : ¬ 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) t x hx, hvx, hvxm1, hvxp1]
          nlinarith [ht, Int.natCast_nonneg x]
        rw [hstep, if_neg hnf, hvx]; ring
      · have hxlt2 : (x : ℤ) < blockEdge d t := lt_of_le_of_ne h2 hxb
        have hvxp1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x + 1)) = (t : ℤ) := by
          refine block_eq d hd t (x + 1) (by omega) ?_
          exact_mod_cast (by omega : (x : ℤ) + 1 ≤ blockEdge d t)
        have htc : t + 1 ≤ tCrit d := by
          by_contra hc
          have hcle : tCrit d ≤ t := by omega
          have := blockEdge_succ_eq_pred_sub_one d t hcle
          omega
        have hb1 : blockEdge d (t + 1) = ((d : ℤ) - 1) / (t : ℤ) := by
          have := blockEdge_of_le d (t + 1) (by omega) htc
          simpa using this
        have hov := ediv_add_one_mul_gt ((d : ℤ) - 1) (t : ℤ) (by exact_mod_cast ht)
        have hxge : ((d : ℤ) - 1) / (t : ℤ) + 1 ≤ (x : ℤ) := by
          rw [← hb1]; omega
        have htx : (d : ℤ) - 1 < (x : ℤ) * (t : ℤ) := by
          have hmono : (((d : ℤ) - 1) / (t : ℤ) + 1) * (t : ℤ) ≤ (x : ℤ) * (t : ℤ) :=
            mul_le_mul_of_nonneg_right hxge (by exact_mod_cast Nat.zero_le t)
          linarith [hov, hmono]
        have hnf : ¬ 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) t x hx, hvx, hvxm1, hvxp1]
          nlinarith [htx]
        rw [hstep, if_neg hnf, hvx]; ring

/-- Inside a window of length at least `2`, the front times the position
exceeds `d - 1`; this is the bound from the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`, applied at
the window's own right edge, not only its interior. -/
theorem window_mul_gt (d s x : ℕ) (_hd : 1 ≤ d) (hx : x ≤ d)
    (h1 : blockEdge d (s + 1) < (x : ℤ)) (h2 : (x : ℤ) ≤ blockEdge d s)
    (hlen : blockEdge d (s + 1) + 1 < blockEdge d s) :
    (d : ℤ) - 1 < (x : ℤ) * (s : ℤ) := by
  have hs1 : 1 ≤ s := by
    by_contra hc
    have hs0 : s = 0 := by omega
    subst hs0
    have hb : blockEdge d 1 = (d : ℤ) := rfl
    rw [hb] at h1
    omega
  have htc : s + 1 ≤ tCrit d := by
    by_contra hc
    have hcle : tCrit d ≤ s := by omega
    have := blockEdge_succ_eq_pred_sub_one d s hcle
    omega
  have hb1 : blockEdge d (s + 1) = ((d : ℤ) - 1) / (s : ℤ) := by
    have := blockEdge_of_le d (s + 1) (by omega) htc
    simpa using this
  have hov := ediv_add_one_mul_gt ((d : ℤ) - 1) (s : ℤ) (by exact_mod_cast hs1)
  have hxge : ((d : ℤ) - 1) / (s : ℤ) + 1 ≤ (x : ℤ) := by
    rw [← hb1]; omega
  have hmono : (((d : ℤ) - 1) / (s : ℤ) + 1) * (s : ℤ) ≤ (x : ℤ) * (s : ℤ) :=
    mul_le_mul_of_nonneg_right hxge (by exact_mod_cast Nat.zero_le s)
  linarith [hov, hmono]

/-- The value of the odometer at time `s + 1`, at a position `z` inside
window `s` (`(z:ℤ) ≤ blockEdge d s`): either `z` is still in the firing block
at that time (giving `s + 1`) or it has just been vacated (giving `s`). -/
theorem shifted_value (d : ℕ) (hd : 1 ≤ d) (s : ℕ) (hs1 : 1 ≤ s) (z : ℕ) (hz : z ≤ d)
    (hzs : (z : ℤ) ≤ blockEdge d s) :
    ((z : ℤ) ≤ blockEdge d (s + 1) ∧
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d z) = (s : ℤ) + 1) ∨
    (blockEdge d (s + 1) < (z : ℤ) ∧
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d z) = (s : ℤ)) := by
  by_cases hc : (z : ℤ) ≤ blockEdge d (s + 1)
  · left
    refine ⟨hc, ?_⟩
    have := block_eq d hd (s + 1) z hz hc
    rw [this]; push_cast; ring
  · right
    push Not at hc
    refine ⟨hc, ?_⟩
    rw [beyond_block_eq d hd s z hs1 hz hc hzs]
    exact block_eq d hd s z hz hzs

/-- The base case's ripple clause for shift `1` (the front's first step
after formation), the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`: proved by strong induction on the
front `s` alone, since the only cross-front fact it needs (the previous
front's own first step) is at a strictly smaller front. General shifts
(`ripple_shift`, shift `k ≥ 2`) need `s + 1` as well as `s - 1`, so they
require the outer induction to run on the absolute time instead; that
combined statement is not yet closed (see FINDINGS.md). -/
theorem ripple_one_step (d : ℕ) (hd : 1 ≤ d) :
    ∀ s : ℕ, ∀ x : ℕ, 1 ≤ x → x ≤ d →
      blockEdge d (s + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d s →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 2) (radial d x)
        = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - 1)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
    intro x hx1 hxd h1 h2
    have hs1 : 1 ≤ s := by
      by_contra hc
      have hs0 : s = 0 := by omega
      subst hs0
      simp only [Nat.zero_add] at h1
      have hb1 : blockEdge d 1 = (d : ℤ) := rfl
      omega
    have hvx : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d x) = (s : ℤ) := by
      rw [beyond_block_eq d hd s x hs1 hxd h1 h2]
      exact block_eq d hd s x hxd h2
    by_cases hxdg : x = d
    · have hxeqR : (x : ℤ) = blockEdge d s := by
        have hble := blockEdge_le_self d s hd
        omega
      have hz : (d : ℤ) - (x : ℤ) = 0 := by omega
      by_cases hbL : (x : ℤ) - 1 ≤ blockEdge d (s + 1)
      · have hvxm1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - 1))
            = ((s + 1 : ℕ) : ℤ) := block_eq d hd (s + 1) (x - 1) (by omega) (by omega)
        have hfire : 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) x hxd, hz, zero_mul,
            hvx, hvxm1]
          push_cast
          ring_nf
          have hbnd := blockEdge_window_le' d s x hd hxd h2
          ring_nf at hbnd
          nlinarith [hbnd, hz]
        have hgo := ripple_step_ge d (s + 1) x hd hxd hfire (by omega)
        simpa using hgo
      · have hgt : blockEdge d (s + 1) < ((x - 1 : ℕ) : ℤ) := by omega
        have hle : ((x - 1 : ℕ) : ℤ) ≤ blockEdge d s := by omega
        have hvxm1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - 1))
            = (s : ℤ) := by
          rw [beyond_block_eq d hd s (x - 1) hs1 (by omega) hgt hle]
          exact block_eq d hd s (x - 1) (by omega) hle
        have hlen : blockEdge d (s + 1) + 1 < blockEdge d s := by omega
        have hnf : ¬ 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) x hxd, hz, zero_mul,
            hvx, hvxm1]
          ring_nf
          have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
          ring_nf at hbnd
          nlinarith [hbnd, hz]
        have hlt := ripple_step_lt d (s + 1) x hd hxd hnf (by omega)
        simpa using hlt
    · have hvxp1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x + 1))
          = (s : ℤ) := by
        by_cases hbR : (x : ℤ) < blockEdge d s
        · rw [beyond_block_eq d hd s (x + 1) hs1 (by omega) (by omega) (by omega)]
          exact block_eq d hd s (x + 1) (by omega) (by omega)
        · have hxeqR : (x : ℤ) = blockEdge d s := by omega
          have hxltd : (x : ℤ) < (d : ℤ) := by
            have hxd2 : x ≠ d := hxdg
            omega
          have hcase : s ≠ 1 := by
            intro hc
            subst hc
            have hb1 : blockEdge d 1 = (d : ℤ) := rfl
            omega
          have hsm1pos : 1 ≤ s - 1 := by omega
          have hsm1lt : s - 1 < s := by omega
          have hstrict := blockEdge_strict d (s - 1) hd hsm1pos
          have he0 : s - 1 + 1 = s := by omega
          rw [he0] at hstrict
          have hcond2 : blockEdge d (s - 1 + 1) < ((x + 1 : ℕ) : ℤ) := by
            rw [he0]; push_cast; omega
          have hcond1 : ((x + 1 : ℕ) : ℤ) ≤ blockEdge d (s - 1) := by
            push_cast; omega
          have hthis := ihs (s - 1) hsm1lt (x + 1) (by omega) (by omega) hcond2 hcond1
          have he1 : s - 1 + 2 = s + 1 := by omega
          rw [he1, he0] at hthis
          have hxk : x + 1 - 1 = x := by omega
          rw [hxk] at hthis
          rw [hthis]
          exact block_eq d hd s x hxd h2
      by_cases hbL : (x : ℤ) - 1 ≤ blockEdge d (s + 1)
      · have hvxm1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - 1))
            = ((s + 1 : ℕ) : ℤ) := block_eq d hd (s + 1) (x - 1) (by omega) (by omega)
        have hfire : 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) x hxd, hvx, hvxm1, hvxp1]
          push_cast
          ring_nf
          have hbnd := blockEdge_window_le' d s x hd hxd h2
          ring_nf at hbnd
          nlinarith [hbnd]
        have hgo := ripple_step_ge d (s + 1) x hd hxd hfire (by omega)
        simpa using hgo
      · have hgt : blockEdge d (s + 1) < ((x - 1 : ℕ) : ℤ) := by omega
        have hle : ((x - 1 : ℕ) : ℤ) ≤ blockEdge d s := by omega
        have hvxm1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - 1))
            = (s : ℤ) := by
          rw [beyond_block_eq d hd s (x - 1) hs1 (by omega) hgt hle]
          exact block_eq d hd s (x - 1) (by omega) hle
        have hlen : blockEdge d (s + 1) + 1 < blockEdge d s := by omega
        have hnf : ¬ 2 * (d : ℤ) ≤
            sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d x) := by
          rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) x hxd, hvx, hvxm1, hvxp1]
          ring_nf
          have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
          ring_nf at hbnd
          nlinarith [hbnd]
        have hlt := ripple_step_lt d (s + 1) x hd hxd hnf (by omega)
        simpa using hlt

/-- `blockEdge d 2 = d - 1` unconditionally: both branches of the definition
agree, the subsection labelled `subsec:M2` in `dimred-corrected-arxiv.tex`. -/
theorem blockEdge_two (d : ℕ) : blockEdge d 2 = (d : ℤ) - 1 := by
  have hdef : blockEdge d 2 = if 2 ≤ tCrit d then ((d : ℤ) - 1) / 1 else blockEdge d 1 - 1 := rfl
  have h1 : blockEdge d 1 = (d : ℤ) := rfl
  rw [hdef, h1]
  split_ifs with h
  · norm_num
  · rfl

-- the strong induction over the shift unfolds the ripple relation at two smaller
-- shifts at every step, which needs the extra budget
set_option maxHeartbeats 4000000 in
/-- The general-shift ripple relation, the proof of the statement labelled `prop:base_case` in `dimred-corrected-arxiv.tex`:
the profile at absolute time `s + k + 1` is the profile at time `s + 1`, shifted
outward by the whole shift `k`, for every `k`, not only `k = 1`
(`ripple_one_step`). Proved by strong induction on `k`, using the smaller shift
`k - 1` at the same front `s` for the window's interior and the smaller shift
`k - 2` at the next front `s + 1` for its left edge, nested inside a strong
induction on `s` for the window's right edge (exactly as in `ripple_one_step`,
which is the case `k = 1`). -/
theorem ripple_shift (d : ℕ) (hd : 1 ≤ d) :
    ∀ k s x : ℕ, k ≤ x → x ≤ d →
      blockEdge d (s + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d s →
      odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + k + 1) (radial d x)
        = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
      intro x hkx hxd h1 h2
      match k with
      | 0 => simp
      | 1 => simpa using ripple_one_step d hd s x hkx hxd h1 h2
      | (n + 2) =>
        have hs1 : 1 ≤ s := by
          by_contra hc
          have hs0 : s = 0 := by omega
          subst hs0
          simp only [Nat.zero_add] at h1
          have hb1 : blockEdge d 1 = (d : ℤ) := rfl
          have hb0 : blockEdge d 0 = (d : ℤ) := rfl
          omega
        -- The value at a position strictly inside window `s`, obtained from the
        -- shift `n + 1` at the same front `s`.
        have keyval : ∀ pos : ℕ, n + 1 ≤ pos → pos ≤ d →
            blockEdge d (s + 1) < (pos : ℤ) → (pos : ℤ) ≤ blockEdge d s →
            (((pos - (n + 1) : ℕ) : ℤ) ≤ blockEdge d (s + 1) ∧
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d pos)
                  = (s : ℤ) + 1) ∨
            (blockEdge d (s + 1) < ((pos - (n + 1) : ℕ) : ℤ) ∧
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d pos)
                  = (s : ℤ)) := by
          intro pos hpos1 hposd hposgt hposle
          have hq := ihk (n + 1) (by omega) s pos hpos1 hposd hposgt hposle
          have heq : s + (n + 1) + 1 = s + (n + 2) := by omega
          rw [heq] at hq
          have hwle : ((pos - (n + 1) : ℕ) : ℤ) ≤ blockEdge d s := by
            have hle : pos - (n + 1) ≤ pos := by omega
            calc ((pos - (n + 1) : ℕ) : ℤ) ≤ (pos : ℤ) := by exact_mod_cast hle
              _ ≤ blockEdge d s := hposle
          rcases shifted_value d hd s hs1 (pos - (n + 1)) (by omega) hwle with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exact Or.inl ⟨hA, by rw [hq]; exact hB⟩
          · exact Or.inr ⟨hA, by rw [hq]; exact hB⟩
        -- The value just beyond that window, at the edge `x - 1 = blockEdge d (s+1)`,
        -- obtained from the shift `n` at the next front `s + 1`.
        have boundaryval : blockEdge d (s + 1) = ((x - 1 : ℕ) : ℤ) →
            ((((x - 1 - n : ℕ) : ℤ) ≤ blockEdge d (s + 2) ∧
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d (x - 1))
                  = (s : ℤ) + 2) ∨
            (blockEdge d (s + 2) < ((x - 1 - n : ℕ) : ℤ) ∧
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d (x - 1))
                  = (s : ℤ) + 1)) := by
          intro hbeq
          have hq := ihk n (by omega) (s + 1) (x - 1) (by omega) (by omega)
            (by
              have hstrict := blockEdge_strict d (s + 1) hd (by omega)
              omega)
            (by omega)
          have heq1 : s + 1 + n + 1 = s + (n + 2) := by omega
          have heq2 : s + 1 + 1 = s + 2 := by omega
          rw [heq1, heq2] at hq
          have hwle : ((x - 1 - n : ℕ) : ℤ) ≤ blockEdge d (s + 1) := by
            have hle : x - 1 - n ≤ x - 1 := by omega
            calc ((x - 1 - n : ℕ) : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by exact_mod_cast hle
              _ = blockEdge d (s + 1) := hbeq.symm
          rcases shifted_value d hd (s + 1) (by omega) (x - 1 - n) (by omega) hwle
            with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · refine Or.inl ⟨?_, ?_⟩
            · have heqb : s + 1 + 1 = s + 2 := by omega
              rwa [heqb] at hA
            · rw [hq, hB]; push_cast; ring
          · refine Or.inr ⟨?_, ?_⟩
            · have heqb : s + 1 + 1 = s + 2 := by omega
              rwa [heqb] at hA
            · rw [hq, hB]; push_cast; ring
        -- The value one beyond the right edge `x = blockEdge d s`, obtained from
        -- the same shift `k` at the previous front `s - 1`.
        have rightval : (x : ℤ) = blockEdge d s → x ≠ d →
            odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d (x + 1))
              = (s : ℤ) := by
          intro hxeqR hxne
          have hsne1 : s ≠ 1 := by
            intro hc
            subst hc
            have hb1 : blockEdge d 1 = (d : ℤ) := rfl
            rw [hb1] at hxeqR
            exact hxne (by exact_mod_cast hxeqR)
          have hs2 : 2 ≤ s := by omega
          have hcond1 : blockEdge d (s - 1 + 1) < ((x + 1 : ℕ) : ℤ) := by
            have heq : s - 1 + 1 = s := by omega
            rw [heq, ← hxeqR]
            push_cast; omega
          have hcond2 : ((x + 1 : ℕ) : ℤ) ≤ blockEdge d (s - 1) := by
            have hstrict := blockEdge_strict d (s - 1) hd (by omega)
            have heq : s - 1 + 1 = s := by omega
            rw [heq] at hstrict
            rw [← hxeqR] at hstrict
            push_cast; omega
          have hq := ihs (s - 1) (by omega) (x + 1) (by omega) (by omega) hcond1 hcond2
          have heq1 : s - 1 + (n + 2) + 1 = s + (n + 2) := by omega
          have heq2 : s - 1 + 1 = s := by omega
          rw [heq1, heq2] at hq
          rw [hq]
          refine block_eq d hd s (x + 1 - (n + 2)) (by omega) ?_
          have hle : x + 1 - (n + 2) ≤ x := by omega
          have hcast : ((x + 1 - (n + 2) : ℕ) : ℤ) ≤ (x : ℤ) := by exact_mod_cast hle
          omega
        by_cases hxdg : x = d
        · -- `x = d`: forces `s = 1`, and `blockEdge d 2 = d - 1`, so `x - 1` is
          -- always the left edge of window `s + 1`.
          have hs_eq : s = 1 := by
            have hle : blockEdge d s ≤ (d : ℤ) := blockEdge_le_self d s hd
            have hxeq : (x : ℤ) = (d : ℤ) := by exact_mod_cast hxdg
            by_contra hne
            have hs2 : 2 ≤ s := by omega
            have hstep : blockEdge d s ≤ blockEdge d 2 := blockEdge_antitone_le d hs2
            rw [blockEdge_two] at hstep
            omega
          have hbeq : blockEdge d (s + 1) = ((x - 1 : ℕ) : ℤ) := by
            rw [hs_eq]
            have h22 : (1 : ℕ) + 1 = 2 := rfl
            rw [h22, blockEdge_two]
            have : x - 1 = d - 1 := by omega
            rw [this]
            have hd1 : 1 ≤ d := hd
            push_cast [Nat.cast_sub hd1]
            ring
          have hB : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
              = (s : ℤ) + 1 := by
            rcases keyval x (by omega) hxd h1 h2 with ⟨_, hv⟩ | ⟨hcon, _⟩
            · exact hv
            · exfalso
              have hle : x - (n + 1) ≤ x - 1 := by omega
              have hcast : ((x - (n + 1) : ℕ) : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by exact_mod_cast hle
              omega
          have hxz : (x : ℤ) = (d : ℤ) := by exact_mod_cast hxdg
          have hz : (d : ℤ) - (x : ℤ) = 0 := by omega
          have hfinal : ∀ Aval : ℤ,
              odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d (x - 1)) = Aval →
              (Aval = (s : ℤ) + 2 ∨ Aval = (s : ℤ) + 1) →
              odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2) + 1) (radial d x)
                = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2))) := by
            intro Aval hAval hcase
            have hnf : ¬ 2 * (d : ℤ) ≤
                sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) := by
              rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                hz, zero_mul, hAval, hB]
              rcases hcase with hc | hc <;> rw [hc] <;> nlinarith [hxz, hs1]
            have h0 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2) + 1) (radial d x)
                = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) := by
              rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
                (inCube_radial d x), if_neg hnf]
              ring
            rw [h0, hB]
            have hyle : ((x - (n + 2) : ℕ) : ℤ) ≤ blockEdge d (s + 1) := by
              have hle : x - (n + 2) ≤ x - 1 := by omega
              calc ((x - (n + 2) : ℕ) : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by exact_mod_cast hle
                _ = blockEdge d (s + 1) := hbeq.symm
            exact (block_eq d hd (s + 1) (x - (n + 2)) (by omega) hyle).symm
          rcases boundaryval hbeq with ⟨_, hAval⟩ | ⟨_, hAval⟩
          · exact hfinal _ hAval (Or.inl rfl)
          · exact hfinal _ hAval (Or.inr rfl)
        · -- `x ≠ d`
          have htargetle : ((x - (n + 2) : ℕ) : ℤ) ≤ blockEdge d s := by
            have hle : x - (n + 2) ≤ x := by omega
            have hcast : ((x - (n + 2) : ℕ) : ℤ) ≤ (x : ℤ) := by exact_mod_cast hle
            omega
          have htarget := shifted_value d hd s hs1 (x - (n + 2)) (by omega) htargetle
          by_cases hbL : (x : ℤ) - 1 ≤ blockEdge d (s + 1)
          · -- boundary: `x - 1 = blockEdge d (s + 1)` exactly
            have hbeq : blockEdge d (s + 1) = ((x - 1 : ℕ) : ℤ) := by
              have hcast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
                have hx1 : 1 ≤ x := by omega
                push_cast [Nat.cast_sub hx1]; ring
              omega
            have hB : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
                = (s : ℤ) + 1 := by
              rcases keyval x (by omega) hxd h1 h2 with ⟨_, hv⟩ | ⟨hcon, _⟩
              · exact hv
              · exfalso
                have hle : x - (n + 1) ≤ x - 1 := by omega
                have hcast : ((x - (n + 1) : ℕ) : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by exact_mod_cast hle
                omega
            have htarget_boundary :
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                  = (s : ℤ) + 1 := by
              rcases htarget with ⟨_, htv⟩ | ⟨htcon, _⟩
              · exact htv
              · exfalso
                have hle : x - (n + 2) ≤ x - 1 := by omega
                have hcast : ((x - (n + 2) : ℕ) : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by exact_mod_cast hle
                omega
            have closeBoundary : (¬ 2 * (d : ℤ) ≤
                sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)) →
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2) + 1) (radial d x)
                  = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2))) := by
              intro hnf
              rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
                (inCube_radial d x), if_neg hnf, hB, htarget_boundary]
              ring
            have hzstrict : blockEdge d (s + 1 + 1) < blockEdge d (s + 1) :=
              blockEdge_strict d (s + 1) hd (by omega)
            by_cases hbR : (x : ℤ) < blockEdge d s
            · -- not the right edge: window length at least `2`
              have hlen : blockEdge d (s + 1) + 1 < blockEdge d s := by omega
              rcases boundaryval hbeq with ⟨hAcond, hAval⟩ | ⟨hAcond, hAval⟩
              · -- `A = s + 2`
                rcases keyval (x + 1) (by omega) (by omega) (by omega) (by omega)
                  with ⟨hCcond, hCval⟩ | ⟨hCcond, hCval⟩
                · -- `C = s + 1`: real, no fire (`window_mul_gt`)
                  apply closeBoundary
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hB, hCval]
                  have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
                  nlinarith [hbnd]
                · -- `C = s`: impossible (`blockEdge` strictly decreases)
                  exfalso
                  have heq : s + 1 + 1 = s + 2 := by omega
                  rw [heq] at hzstrict
                  omega
              · -- `A = s + 1`
                rcases keyval (x + 1) (by omega) (by omega) (by omega) (by omega)
                  with ⟨hCcond, hCval⟩ | ⟨hCcond, hCval⟩
                · -- `C = s + 1`: no fire (`window_mul_gt`)
                  apply closeBoundary
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hB, hCval]
                  have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
                  nlinarith [hbnd, hxd]
                · -- `C = s`: no fire, trivial
                  apply closeBoundary
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hB, hCval]
                  nlinarith [hxd, hs1]
            · -- the right edge: window length exactly `1`
              have hC := rightval (by omega) hxdg
              rcases boundaryval hbeq with ⟨hAcond, hAval⟩ | ⟨hAcond, hAval⟩
              · -- `A = s + 2`: no fire, trivial
                apply closeBoundary
                rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                  hAval, hB, hC]
                nlinarith [hxd, hs1]
              · -- `A = s + 1`: no fire, trivial
                apply closeBoundary
                rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                  hAval, hB, hC]
                nlinarith [hxd, hs1]
          · -- interior: `blockEdge d (s + 1) < x - 1`
            have hgt : blockEdge d (s + 1) < ((x - 1 : ℕ) : ℤ) := by omega
            have hlen : blockEdge d (s + 1) + 1 < blockEdge d s := by omega
            have closeNoFire : ∀ Bval Tval : ℤ,
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) = Bval →
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                  = Tval →
                Bval = Tval →
                ¬ 2 * (d : ℤ) ≤
                    sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) →
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2) + 1) (radial d x)
                  = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2))) := by
              intro Bval Tval hBval hTval heq hnf
              rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
                (inCube_radial d x), if_neg hnf, hBval, hTval, heq]
              ring
            have closeFire : ∀ Bval Tval : ℤ,
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) = Bval →
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                  = Tval →
                Bval + 1 = Tval →
                2 * (d : ℤ) ≤
                    sandp d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x) →
                odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2) + 1) (radial d x)
                  = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2))) := by
              intro Bval Tval hBval hTval heq hfire
              rw [odo_succ_eq d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) (radial d x)
                (inCube_radial d x), if_pos hfire, hBval, hTval]
              omega
            rcases keyval (x - 1) (by omega) (by omega) hgt (by omega) with
              ⟨hAcond, hAval⟩ | ⟨hAcond, hAval⟩
            · -- `A = s + 1`
              rcases keyval x (by omega) hxd h1 h2 with ⟨hBcond, hBval⟩ | ⟨hBcond, hBval⟩
              · -- `B = s + 1`: no fire, target `s + 1`
                have htarget_final :
                    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                      = (s : ℤ) + 1 := by
                  rcases htarget with ⟨_, htv⟩ | ⟨htcon, _⟩
                  · exact htv
                  · exfalso
                    have hle : x - (n + 2) ≤ x - (n + 1) := by omega
                    have hcast : ((x - (n + 2) : ℕ) : ℤ) ≤ ((x - (n + 1) : ℕ) : ℤ) := by
                      exact_mod_cast hle
                    omega
                by_cases hbR : (x : ℤ) < blockEdge d s
                · rcases keyval (x + 1) (by omega) (by omega) (by omega) (by omega) with
                    ⟨hCcond, hCval⟩ | ⟨hCcond, hCval⟩
                  · -- `C = s + 1`: no fire (`window_mul_gt`)
                    refine closeNoFire _ _ hBval htarget_final rfl ?_
                    intro hf
                    rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                      hAval, hBval, hCval] at hf
                    have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
                    nlinarith [hbnd, hxd]
                  · -- `C = s`: no fire, trivial (`++-`)
                    refine closeNoFire _ _ hBval htarget_final rfl ?_
                    intro hf
                    rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                      hAval, hBval, hCval] at hf
                    nlinarith [hxd, hs1]
                · have hC := rightval (by omega) hxdg
                  refine closeNoFire _ _ hBval htarget_final rfl ?_
                  intro hf
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hBval, hC] at hf
                  nlinarith [hxd, hs1]
              · -- `B = s`: fire, target `s + 1 = A`
                have htarget_final :
                    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                      = (s : ℤ) + 1 := by
                  rcases htarget with ⟨_, htv⟩ | ⟨htcon, _⟩
                  · exact htv
                  · exfalso; omega
                by_cases hbR : (x : ℤ) < blockEdge d s
                · rcases keyval (x + 1) (by omega) (by omega) (by omega) (by omega) with
                    ⟨hCcond, hCval⟩ | ⟨hCcond, hCval⟩
                  · -- `C = s + 1`: impossible
                    exfalso
                    have hle : x - (n + 1) ≤ x + 1 - (n + 1) := by omega
                    have hcast : ((x - (n + 1) : ℕ) : ℤ) ≤ ((x + 1 - (n + 1) : ℕ) : ℤ) := by
                      exact_mod_cast hle
                    omega
                  · -- `C = s`: fire, real (`+--`)
                    refine closeFire _ _ hBval htarget_final (by omega) ?_
                    rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                      hAval, hBval, hCval]
                    have hbnd := blockEdge_window_le' d s x hd hxd h2
                    nlinarith [hbnd]
                · have hC := rightval (by omega) hxdg
                  refine closeFire _ _ hBval htarget_final (by omega) ?_
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hBval, hC]
                  have hbnd := blockEdge_window_le' d s x hd hxd h2
                  nlinarith [hbnd]
            · -- `A = s`
              rcases keyval x (by omega) hxd h1 h2 with ⟨hBcond, hBval⟩ | ⟨hBcond, hBval⟩
              · -- `B = s + 1`: impossible
                exfalso
                have heq : x - (n + 2) + 1 = x - (n + 1) := by omega
                have hcast : ((x - (n + 2) : ℕ) : ℤ) + 1 = ((x - (n + 1) : ℕ) : ℤ) := by
                  have := heq
                  exact_mod_cast this
                omega
              · -- `B = s`: no fire, target `s`
                have htarget_final :
                    odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (n + 2)))
                      = (s : ℤ) := by
                  rcases htarget with ⟨htv_le, _⟩ | ⟨_, htv⟩
                  · exfalso; omega
                  · exact htv
                by_cases hbR : (x : ℤ) < blockEdge d s
                · rcases keyval (x + 1) (by omega) (by omega) (by omega) (by omega) with
                    ⟨hCcond, hCval⟩ | ⟨hCcond, hCval⟩
                  · -- `C = s + 1`: impossible
                    exfalso
                    have hle : x - (n + 1) ≤ x + 1 - (n + 1) := by omega
                    have hcast : ((x - (n + 1) : ℕ) : ℤ) ≤ ((x + 1 - (n + 1) : ℕ) : ℤ) := by
                      exact_mod_cast hle
                    omega
                  · -- `C = s`: no fire, real (`---`)
                    refine closeNoFire _ _ hBval htarget_final rfl ?_
                    intro hf
                    rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                      hAval, hBval, hCval] at hf
                    have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
                    nlinarith [hbnd]
                · have hC := rightval (by omega) hxdg
                  refine closeNoFire _ _ hBval htarget_final rfl ?_
                  intro hf
                  rw [sandp, lap_radial d (2 * (d : ℤ) + ((d : ℤ) - 1)) (s + (n + 2)) x hxd,
                    hAval, hBval, hC] at hf
                  have hbnd := window_mul_gt d s x hd hxd h1 h2 hlen
                  nlinarith [hbnd]
end DimRed
