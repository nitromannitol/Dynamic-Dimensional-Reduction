/-
Terminal finiteness and the second display of Theorem 1.1(i) of `dimred.tex`.
The stabilisation argument supplies the finite terminal odometers needed to
pass the finite-time dimensional-reduction identity to the limit; the final
reflection identity is kept as an explicit hypothesis, as in
`dimred.tex:1178-1180` and `dimred.tex:163-164`.
-/
import DimRed.Frozen.Prelim.ParabolicComparison
import DimRed.Support.AxisStep
import DimRed.Support.Stabilize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

private def terminalQuad (d N : ℕ) (x : Site d) : ℤ :=
  Finset.univ.sum (fun i : Fin d => ((N : ℤ) + 1) ^ 2 - (x i) ^ 2)

private def terminalBarrier (d N : ℕ) (x : Site d) : ℤ :=
  if inCube d N x then terminalQuad d N x else 0

private theorem terminal_coord_bound (d N : ℕ) (x : Site d)
    (hx : inCube d N x) (i : Fin d) :
    -(N : ℤ) ≤ x i ∧ x i ≤ (N : ℤ) := by
  have hi := hx i
  simp only [loCoord, hiCoord, sideHalf] at hi
  omega

private theorem terminal_quad_nonneg (d N : ℕ) (x : Site d)
    (hx : inCube d N x) : 0 ≤ terminalQuad d N x := by
  unfold terminalQuad
  refine Finset.sum_nonneg fun i _ => ?_
  have hi := terminal_coord_bound d N x hx i
  nlinarith

private theorem terminal_quad_step_nonneg (d N : ℕ) (x : Site d)
    (hx : inCube d N x) (i : Fin d) :
    0 ≤ terminalQuad d N (x + unit i) := by
  unfold terminalQuad
  refine Finset.sum_nonneg fun k _ => ?_
  have hk := terminal_coord_bound d N x hx k
  have hstepk := add_unit_apply d x i k
  rw [hstepk]
  by_cases hki : k = i
  · simp only [if_pos hki]
    nlinarith
  · simp only [if_neg hki]
    nlinarith

private theorem terminal_quad_sub_step_nonneg (d N : ℕ) (x : Site d)
    (hx : inCube d N x) (i : Fin d) :
    0 ≤ terminalQuad d N (x - unit i) := by
  unfold terminalQuad
  refine Finset.sum_nonneg fun k _ => ?_
  have hk := terminal_coord_bound d N x hx k
  have hstepk := sub_unit_apply d x i k
  rw [hstepk]
  by_cases hki : k = i
  · simp only [if_pos hki]
    nlinarith
  · simp only [if_neg hki]
    nlinarith

private theorem terminal_quad_neighbour_sum (d N : ℕ) (x : Site d) :
    nbrSum (terminalQuad d N) x =
      2 * (d : ℤ) * terminalQuad d N x - 2 * (d : ℤ) := by
  unfold nbrSum terminalQuad
  have hterm : ∀ i : Fin d,
      (Finset.univ.sum (fun k : Fin d =>
          ((N : ℤ) + 1) ^ 2 - (x + unit i) k ^ 2) +
        Finset.univ.sum (fun k : Fin d =>
          ((N : ℤ) + 1) ^ 2 - (x - unit i) k ^ 2)) =
        2 * (Finset.univ.sum (fun k : Fin d =>
          ((N : ℤ) + 1) ^ 2 - (x k) ^ 2)) - 2 := by
    intro i
    rw [← Finset.sum_add_distrib]
    have hpoint : ∀ k : Fin d,
        (((N : ℤ) + 1) ^ 2 - (x + unit i) k ^ 2) +
            (((N : ℤ) + 1) ^ 2 - (x - unit i) k ^ 2) =
          2 * (((N : ℤ) + 1) ^ 2 - (x k) ^ 2) -
            (if k = i then 2 else 0) := by
      intro k
      rw [add_unit_apply, sub_unit_apply]
      by_cases hki : k = i
      · simp only [if_pos hki]
        ring
      · simp only [if_neg hki]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hpoint k)]
    rw [Finset.sum_sub_distrib]
    have hif : ∑ k : Fin d, (if k = i then (2 : ℤ) else 0) = 2 := by
      simp
    rw [hif, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_const, Finset.card_univ]
  ring

private theorem terminal_barrier_lap_le (d N : ℕ) (_hd : 1 ≤ d) (x : Site d)
    (hx : inCube d N x) :
    lap (terminalBarrier d N) x ≤ -2 * (d : ℤ) := by
  have hplus : ∀ i : Fin d,
      terminalBarrier d N (x + unit i) ≤ terminalQuad d N (x + unit i) := by
    intro i
    by_cases hi : inCube d N (x + unit i)
    · simp only [terminalBarrier, if_pos hi]
      exact le_rfl
    · rw [terminalBarrier, if_neg hi]
      exact terminal_quad_step_nonneg d N x hx i
  have hminus : ∀ i : Fin d,
      terminalBarrier d N (x - unit i) ≤ terminalQuad d N (x - unit i) := by
    intro i
    by_cases hi : inCube d N (x - unit i)
    · simp only [terminalBarrier, if_pos hi]
      exact le_rfl
    · rw [terminalBarrier, if_neg hi]
      exact terminal_quad_sub_step_nonneg d N x hx i
  have hnb : nbrSum (terminalBarrier d N) x ≤ nbrSum (terminalQuad d N) x := by
    unfold nbrSum
    refine Finset.sum_le_sum fun i _ => ?_
    linarith [hplus i, hminus i]
  have hself : terminalBarrier d N x = terminalQuad d N x := by
    simp [terminalBarrier, hx]
  rw [lap, hself]
  rw [terminal_quad_neighbour_sum] at hnb
  linarith

private theorem terminal_eventually_constant (f : ℕ → ℕ) (K : ℕ)
    (hmono : ∀ m n, m ≤ n → f m ≤ f n) (hbound : ∀ n, f n ≤ K) :
    ∃ T, ∀ n, f (T + n) = f T := by
  induction K with
  | zero =>
      refine ⟨0, ?_⟩
      intro n
      have hn := hbound n
      have h0 := hbound 0
      have hn0 : f n = 0 := Nat.eq_zero_of_le_zero hn
      have h00 : f 0 = 0 := Nat.eq_zero_of_le_zero h0
      calc
        f (0 + n) = f n := by simp
        _ = 0 := hn0
        _ = f 0 := h00.symm
  | succ K ih =>
      by_cases hreach : ∃ n, f n = K + 1
      · obtain ⟨T, hT⟩ := hreach
        refine ⟨T, ?_⟩
        intro n
        have hle := hbound (T + n)
        have hmono' := hmono T (T + n) (by omega)
        omega
      · have hbound' : ∀ n, f n ≤ K := by
          intro n
          have hn : f n ≠ K + 1 := by
            intro hn
            exact hreach ⟨n, hn⟩
          have hle := hbound n
          omega
        exact ih hbound'

private theorem terminal_finset_common_stable {d : ℕ}
    (g : ℕ → Site d → ℤ) (S : Finset (Site d))
    (hS : ∀ y ∈ S, ∃ T, ∀ n, g (T + n) y = g T y) :
    ∃ T, ∀ y ∈ S, ∀ n, g (T + n) y = g T y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert a S ha ih =>
      obtain ⟨Ta, hTa⟩ := hS a (Finset.mem_insert_self a S)
      obtain ⟨Ts, hTs⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
      refine ⟨max Ta Ts, ?_⟩
      intro y hy n
      simp only [Finset.mem_insert] at hy
      rcases hy with hya | hy
      · subst y
        have h1 := hTa (max Ta Ts - Ta + n)
        have h2 := hTa (max Ta Ts - Ta)
        have e1 : max Ta Ts + n = Ta + (max Ta Ts - Ta + n) := by omega
        have e2 : max Ta Ts = Ta + (max Ta Ts - Ta) := by omega
        calc
          g (max Ta Ts + n) a = g (Ta + (max Ta Ts - Ta + n)) a := by rw [e1]
          _ = g Ta a := h1
          _ = g (Ta + (max Ta Ts - Ta)) a := h2.symm
          _ = g (max Ta Ts) a := by exact (congrArg (fun k => g k a) e2).symm
      · have h1 := hTs y hy (max Ta Ts - Ts + n)
        have h2 := hTs y hy (max Ta Ts - Ts)
        have e1 : max Ta Ts + n = Ts + (max Ta Ts - Ts + n) := by omega
        have e2 : max Ta Ts = Ts + (max Ta Ts - Ts) := by omega
        calc
          g (max Ta Ts + n) y = g (Ts + (max Ta Ts - Ts + n)) y := by rw [e1]
          _ = g Ts y := h1
          _ = g (Ts + (max Ta Ts - Ts)) y := h2.symm
          _ = g (max Ta Ts) y := by exact (congrArg (fun k => g k y) e2).symm

theorem odoInf_finite (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    ∃ T, odo d N s₀ (T + 1) = odo d N s₀ T := by
  let u : ℕ → Site d → ℤ := fun _ x => terminalBarrier d N x
  have hu0 : ∀ t y, 0 ≤ u t y := by
    intro t y
    by_cases hy : inCube d N y
    · simpa [u, terminalBarrier, hy] using terminal_quad_nonneg d N y hy
    · simp [u, terminalBarrier, hy]
  have hu1 : ∀ t y, ¬ inCube d N y → u t y = 0 := by
    intro t y hy
    simp [u, terminalBarrier, hy]
  have hcon : ∀ (t : ℕ) (y : Site d), inCube d N y →
      (-(2 * (d : ℤ)) * u (t + 1) y + nbrSum (u t) y) + s₀ y
        ≤ 2 * (d : ℤ) - 1 := by
    intro t y hy
    have hlap := terminal_barrier_lap_le d N hd y hy
    have hq : lap (terminalBarrier d N) y =
        -(2 * (d : ℤ)) * u t y + nbrSum (u t) y := by
      simp [u, lap]
    rw [← hq]
    have hs := hs1 y hy
    linarith
  have hcomp := Frozen.parabolic_comparison d N hd s₀ hs0 hs1
  have hupper : ∀ t y, odo d N s₀ t y ≤ u t y :=
    hcomp.2 u hu0 hu1 hcon
  have hsite : ∀ y ∈ cube d N, ∃ T, ∀ n,
      odo d N s₀ (T + n) y = odo d N s₀ T y := by
    intro y hy
    have hycube : inCube d N y := by
      have hmem := Finset.mem_Icc.mp (show y ∈ Finset.Icc
          (fun _ : Fin d => loCoord N) (fun _ : Fin d => hiCoord N) from hy)
      exact fun i => ⟨hmem.1 i, hmem.2 i⟩
    let f : ℕ → ℕ := fun t => (odo d N s₀ t y).toNat
    have hfmono : ∀ m n, m ≤ n → f m ≤ f n := by
      intro m n hmn
      exact Int.toNat_le_toNat (odo_mono d N s₀ hmn y)
    have hfbound : ∀ n, f n ≤ (u n y).toNat := by
      intro n
      exact Int.toNat_le_toNat (hupper n y)
    obtain ⟨T, hT⟩ := terminal_eventually_constant f (u 0 y).toNat hfmono (by
      intro n
      simpa [u] using hfbound n)
    refine ⟨T, ?_⟩
    intro n
    have he := congrArg (fun k : ℕ => (k : ℤ)) (hT n)
    rw [Int.toNat_of_nonneg (odo_nonneg d N s₀ (T + n) y),
      Int.toNat_of_nonneg (odo_nonneg d N s₀ T y)] at he
    exact he
  obtain ⟨T, hT⟩ := terminal_finset_common_stable
    (fun t y => odo d N s₀ t y) (cube d N) hsite
  refine ⟨T, ?_⟩
  funext y
  by_cases hy : inCube d N y
  · have hymem : y ∈ cube d N := by
      rw [cube, Finset.mem_Icc]
      exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩
    simpa using hT y hymem 1
  · rw [odo_eq_zero_outside d N s₀ (T + 1) y hy,
      odo_eq_zero_outside d N s₀ T y hy]

theorem terminal_reduction (N d : ℕ) (_hN : 1 ≤ N) (hd : 1 ≤ d)
    (x : Site d) (_hx : inSimplex d (sideHalf N) x) (_hx2 : ∀ i, 2 ≤ x i)
    (hred : ∀ t : ℕ,
      odoUnif (d + 1) N t (Fin.snoc x 1) = odoUnif d N t x)
    (hreflect :
      odoInfUnif (d + 1) N (Fin.snoc x 2) =
        odoInfUnif (d + 1) N (Fin.snoc x 1)) :
    odoInfUnif (d + 1) N (Fin.snoc x 2) = odoInfUnif d N x := by
  have hfull0 : ∀ y : Site (d + 1), inCube (d + 1) N y →
      0 ≤ (2 * ((d + 1 : ℕ) : ℤ)) := by
    intro y hy
    positivity
  have hfull1 : ∀ y : Site (d + 1), inCube (d + 1) N y →
      2 * ((d + 1 : ℕ) : ℤ) ≤ 2 * (2 * (((d + 1 : ℕ) : ℤ))) - 1 := by
    intro y hy
    have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    norm_num [Nat.cast_add]
  have hlow0 : ∀ y : Site d, inCube d N y → 0 ≤ (2 * (d : ℤ)) := by
    intro y hy
    have hdZ : (0 : ℤ) ≤ (d : ℤ) := by positivity
    linarith
  have hlow1 : ∀ y : Site d, inCube d N y →
      2 * (d : ℤ) ≤ 2 * (2 * (d : ℤ)) - 1 := by
    intro y hy
    have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨Tfull, hfull⟩ := odoInf_finite (d + 1) N (by omega)
    (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) hfull0 hfull1
  obtain ⟨Tlow, hlow⟩ := odoInf_finite d N hd (fun _ => 2 * (d : ℤ)) hlow0 hlow1
  let T := max Tfull Tlow
  have hfullT : odo (d + 1) N (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) (T + 1) =
      odo (d + 1) N (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) T := by
    have h := odo_const_of_stable (d + 1) N
      (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) Tfull hfull (T - Tfull)
    have h' := odo_const_of_stable (d + 1) N
      (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) Tfull hfull (T + 1 - Tfull)
    have e1 : Tfull + (T - Tfull) = T := by dsimp [T]; omega
    have e2 : Tfull + (T + 1 - Tfull) = T + 1 := by
      have hle : Tfull ≤ max Tfull Tlow := Nat.le_max_left _ _
      dsimp [T]
      omega
    rw [e1] at h
    rw [e2] at h'
    exact h'.trans h.symm
  have hlowT : odo d N (fun _ => 2 * (d : ℤ)) (T + 1) =
      odo d N (fun _ => 2 * (d : ℤ)) T := by
    have h := odo_const_of_stable d N (fun _ => 2 * (d : ℤ)) Tlow hlow (T - Tlow)
    have h' := odo_const_of_stable d N (fun _ => 2 * (d : ℤ)) Tlow hlow (T + 1 - Tlow)
    have e1 : Tlow + (T - Tlow) = T := by dsimp [T]; omega
    have e2 : Tlow + (T + 1 - Tlow) = T + 1 := by
      have hle : Tlow ≤ max Tfull Tlow := Nat.le_max_right _ _
      dsimp [T]
      omega
    rw [e1] at h
    rw [e2] at h'
    exact h'.trans h.symm
  have htime := hred T
  have hfiniteFull := odoInf_eq_of_stable (d + 1) N
    (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) T hfullT (Fin.snoc x 1)
  have hfiniteLow := odoInf_eq_of_stable d N (fun _ => 2 * (d : ℤ)) T hlowT x
  rw [hreflect]
  change odoInf (d + 1) N (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) (Fin.snoc x 1) =
    odoInf d N (fun _ => 2 * (d : ℤ)) x
  rw [hfiniteFull, hfiniteLow]
  have htimeZ : odo (d + 1) N (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) T (Fin.snoc x 1) =
      odo d N (fun _ => 2 * (d : ℤ)) T x := by
    simpa [odoUnif] using htime
  have htimeNat := congrArg Int.toNat htimeZ
  exact_mod_cast htimeNat

end DimRed
