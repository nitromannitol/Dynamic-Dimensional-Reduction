module

public import DimRed.Support.EarlyTimes
public import DimRed.Support.AxisStep
public import DimRed.Support.NonnegativeUpdate

@[expose] public section

namespace DimRed

open LatticeProb

/-- The positive orthant of the even cube. -/
def case2Pos (d M : ℕ) (x : Site d) : Prop :=
  ∀ i : Fin d, 1 ≤ x i ∧ x i ≤ (M : ℤ)

/-- The largest positive coordinate, computed as a finite supremum. -/
def case2MaxCoord {d : ℕ} (x : Site d) : ℕ :=
  Finset.univ.sup fun i : Fin d => (x i).toNat

/-- Distance to the positive dissipating face, on the positive orthant. -/
def case2Rho {d : ℕ} (M : ℕ) (x : Site d) : ℕ :=
  M + 1 - case2MaxCoord x

/-- The exact height interval propagated by the parallel toppling update. -/
theorem case2_height_bounds (d M t : ℕ) (hd : 1 ≤ d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    0 ≤ sandpUnif d (2 * M) t x ∧
      sandpUnif d (2 * M) t x ≤ 2 * (2 * (d : ℤ)) - 1 := by
  have h0 : ∀ y, inCube d (2 * M) y → 0 ≤ (fun _ : Site d => 2 * (d : ℤ)) y := by
    intro y hy
    positivity
  have h1 : ∀ y, inCube d (2 * M) y →
      (fun _ : Site d => 2 * (d : ℤ)) y ≤ 2 * (2 * (d : ℤ)) - 1 := by
    intro y hy
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    nlinarith
  exact sandp_bounds d (2 * M) (fun _ => 2 * (d : ℤ)) h0 h1 t x hx

/-- The source-faithful floor update for the actual uniform process. -/
theorem case2_floor_update (d M t : ℕ) (hd : 1 ≤ d) (x : Site d)
    (hx : inCube d (2 * M) x) :
    odoUnif d (2 * M) (t + 1) x =
      (2 * (d : ℤ) + nbrSum (odoUnif d (2 * M) t) x) / (2 * (d : ℤ)) := by
  have h0 : ∀ y, inCube d (2 * M) y →
      0 ≤ (fun _ : Site d => 2 * (d : ℤ)) y := by
    intro y hy
    positivity
  have h1 : ∀ y, inCube d (2 * M) y →
      (fun _ : Site d => 2 * (d : ℤ)) y ≤ 2 * (2 * (d : ℤ)) - 1 := by
    intro y hy
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    nlinarith
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) x =
    (2 * (d : ℤ) + nbrSum (odo d (2 * M) (fun _ => 2 * (d : ℤ)) t) x) /
      (2 * (d : ℤ))
  exact DimRed.bounded_point_update d (2 * M) hd (fun _ => 2 * (d : ℤ)) h0 h1 t x hx

private theorem case2_maxCoord_le {d M : ℕ} {x : Site d} (hx : case2Pos d M x) :
    case2MaxCoord x ≤ M := by
  apply Finset.sup_le
  intro i hi
  have hcast : ((x i).toNat : ℤ) = x i :=
    Int.toNat_of_nonneg (by have := (hx i).1; omega)
  have hle : ((x i).toNat : ℤ) ≤ (M : ℤ) := by rw [hcast]; exact (hx i).2
  exact_mod_cast hle

private theorem case2_coord_le_max {d : ℕ} (x : Site d) (i : Fin d) :
    (x i).toNat ≤ case2MaxCoord x :=
  by simpa [case2MaxCoord] using
    (Finset.le_sup (s := Finset.univ) (f := fun j : Fin d => (x j).toNat)
      (Finset.mem_univ i))

private theorem case2_radius_pos {d M : ℕ} (hd : 1 ≤ d) {x : Site d}
    (hx : case2Pos d M x) : 1 ≤ case2Rho M x := by
  let i : Fin d := ⟨0, by omega⟩
  have hcoord : 1 ≤ (x i).toNat := by
    have hcast : ((x i).toNat : ℤ) = x i :=
      Int.toNat_of_nonneg (by have := (hx i).1; omega)
    have hle : (1 : ℤ) ≤ ((x i).toNat : ℤ) := by rw [hcast]; exact (hx i).1
    exact_mod_cast hle
  have hmax : 1 ≤ case2MaxCoord x := le_trans hcoord (case2_coord_le_max x i)
  have hle := case2_maxCoord_le hx
  dsimp [case2Rho]
  omega

private theorem case2_radius_layer {d M : ℕ} {x : Site d}
    (hx : case2Pos d M x) (i : Fin d) :
    x i + (case2Rho M x : ℤ) ≤ (M : ℤ) + 1 := by
  have hcoord := case2_coord_le_max x i
  have hmax := case2_maxCoord_le hx
  have hnat : (x i).toNat + case2Rho M x ≤ M + 1 := by
    dsimp [case2Rho] at *
    omega
  have hcast : ((x i).toNat : ℤ) = x i :=
    Int.toNat_of_nonneg (by have := (hx i).1; omega)
  have hnat' : ((x i).toNat : ℤ) + (case2Rho M x : ℤ) ≤ (M : ℤ) + 1 := by
    exact_mod_cast hnat
  rw [hcast] at hnat'
  exact hnat'

private theorem case2_max_coord_attained {d : ℕ} (hd : 1 ≤ d) (x : Site d) :
    ∃ i : Fin d, (x i).toNat = case2MaxCoord x := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    let i : Fin d := ⟨0, by omega⟩
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun i : Fin d => (x i).toNat)
  exact ⟨i, heq.symm⟩

private theorem case2_maxCoord_le_of_coord_le {d : ℕ} (x : Site d) (n : ℕ)
    (h : ∀ i : Fin d, (x i).toNat ≤ n) : case2MaxCoord x ≤ n := by
  apply Finset.sup_le
  intro i hi
  exact h i

private theorem case2_first_wait_layer (d M r : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (x : Site d) (hx : case2Pos d M x)
    (hbelow : ∀ i : Fin d, x i ≤ ((M + 1 - r : ℕ) : ℤ))
    (hface : ∃ k : Fin d, x k = ((M + 1 - r : ℕ) : ℤ)) :
    odoUnif d (2 * M) r x = (r : ℤ) ∧
      odoUnif d (2 * M) (r + 1) x = (r : ℤ) := by
  induction r generalizing x with
  | zero =>
      have : False := by
        obtain ⟨k, hk⟩ := hface
        have hk' : x k = (M : ℤ) + 1 := by exact_mod_cast hk
        have := (hx k).2
        omega
      exact this.elim
  | succ r ih =>
      have hcube : inCube d (2 * M) x := by
        intro i
        rw [loCoord_two_mul, hiCoord_two_mul]
        exact ⟨by have := (hx i).1; omega, by have := (hx i).2; omega⟩
      have hearly : odoUnif d (2 * M) (r + 1) x = ((r + 1 : ℕ) : ℤ) := by
        -- This is the interior propagation before the first waiting round.
        have hprop : ∀ n : ℕ, ∀ z : Site d, case2Pos d M z →
            (∀ i : Fin d, z i + (n : ℤ) ≤ (M : ℤ) + 1) →
            odoUnif d (2 * M) n z = (n : ℤ) := by
          intro n
          induction n with
          | zero =>
              intro z hz _
              simp [odoUnif, odo]
          | succ n ihn =>
              intro z hz hdeep
              have hcubez : inCube d (2 * M) z := by
                intro i
                rw [loCoord_two_mul, hiCoord_two_mul]
                exact ⟨by have := (hz i).1; omega, by have := (hz i).2; omega⟩
              have hplus : ∀ i : Fin d,
                  odoUnif d (2 * M) n (z + unit i) = (n : ℤ) := by
                intro i
                by_cases hp : inCube d (2 * M) (z + unit i)
                · have hpos : case2Pos d M (z + unit i) := by
                    intro j
                    by_cases hji : j = i
                    · subst j
                      rw [add_unit_self]
                      constructor
                      · have := (hz i).1
                        omega
                      · have := (hp i).2
                        rw [add_unit_self, hiCoord_two_mul] at this
                        exact this
                    · rw [add_unit_other d z i j hji]
                      exact hz j
                  have hdeep' : ∀ j : Fin d, (z + unit i) j + (n : ℤ) ≤ (M : ℤ) + 1 := by
                    intro j
                    by_cases hji : j = i
                    · subst j
                      rw [add_unit_self]
                      have := hdeep i
                      omega
                    · rw [add_unit_other d z i j hji]
                      have hj := hdeep j
                      omega
                  exact ihn (z + unit i) hpos hdeep'
                · have hiM : z i = (M : ℤ) := by
                    by_contra hne
                    have hiLt : z i + 1 ≤ (M : ℤ) := by have := (hz i).2; omega
                    have hc : inCube d (2 * M) (z + unit i) := by
                      intro j
                      rw [loCoord_two_mul, hiCoord_two_mul]
                      by_cases hji : j = i
                      · subst j
                        rw [add_unit_self]
                        exact ⟨by have := (hz i).1; omega, hiLt⟩
                      · rw [add_unit_other d z i j hji]
                        exact ⟨by have := (hz j).1; omega, (hz j).2⟩
                    exact hp hc
                  have hn0 : n = 0 := by
                    have h := hdeep i
                    rw [hiM] at h
                    omega
                  subst n
                  simp [odoUnif, odo]
              have hminus : ∀ i : Fin d,
                  odoUnif d (2 * M) n (z - unit i) = (n : ℤ) := by
                intro i
                by_cases hi1 : z i = 1
                · have heq : (fun j : Fin d =>
                      if j = i then 1 - (z - unit i) i else (z - unit i) j) = z := by
                    funext j
                    by_cases hji : j = i
                    · subst j
                      rw [ite_eq_left rfl, sub_unit_self, hi1]
                      norm_num
                    · rw [ite_eq_right hji, sub_unit_other d z i j hji]
                  have hsym := odo_reflect_coord d M (2 * (d : ℤ)) n (z - unit i) i
                  rw [heq] at hsym
                  exact hsym.symm.trans (ihn z hz (by
                    intro j
                    have hj := hdeep j
                    omega))
                · have hpos : case2Pos d M (z - unit i) := by
                    intro j
                    by_cases hji : j = i
                    · subst j
                      rw [sub_unit_self]
                      have := (hz i)
                      constructor <;> omega
                    · rw [sub_unit_other d z i j hji]
                      exact hz j
                  have hdeep' : ∀ j : Fin d, (z - unit i) j + (n : ℤ) ≤ (M : ℤ) + 1 := by
                    intro j
                    by_cases hji : j = i
                    · subst j
                      rw [sub_unit_self]
                      have := hdeep i
                      omega
                    · rw [sub_unit_other d z i j hji]
                      have hj := hdeep j
                      omega
                  exact ihn (z - unit i) hpos hdeep'
              have hsum : nbrSum (odoUnif d (2 * M) n) z =
                  2 * (d : ℤ) * (n : ℤ) := by
                unfold nbrSum
                calc
                  (∑ i : Fin d,
                      (odoUnif d (2 * M) n (z + unit i) +
                        odoUnif d (2 * M) n (z - unit i)))
                      = ∑ _i : Fin d, (2 * (n : ℤ)) := by
                          refine Finset.sum_congr rfl ?_
                          intro i _
                          rw [hplus i, hminus i]
                          ring
                  _ = 2 * (d : ℤ) * (n : ℤ) := by
                          simp [Finset.sum_const, Finset.card_univ]
                          ring
              rw [case2_floor_update d M n hd z hcubez, hsum]
              have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
                have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
                linarith
              have hdiv : (2 * (d : ℤ) + 2 * (d : ℤ) * (n : ℤ)) /
                    (2 * (d : ℤ)) = (n + 1 : ℕ) := by
                rw [show 2 * (d : ℤ) + 2 * (d : ℤ) * (n : ℤ) =
                  2 * (d : ℤ) * ((n : ℤ) + 1) by ring]
                exact Int.mul_ediv_cancel_left _ (ne_of_gt hdpos)
              exact hdiv
        have hdeep : ∀ i : Fin d, x i + ((r + 1 : ℕ) : ℤ) ≤ (M : ℤ) + 1 := by
          let j : Fin d := ⟨0, by omega⟩
          have hrM : r ≤ M := by
            have hsubpos : (1 : ℤ) ≤ ((M - r : ℕ) : ℤ) := by
              have hj := hbelow j
              have hsub : M + 1 - (r + 1) = M - r := by omega
              rw [hsub] at hj
              exact le_trans (hx j).1 hj
            have hposNat : 1 ≤ M - r := by exact_mod_cast hsubpos
            omega
          intro i
          have h := hbelow i
          have hsub : M + 1 - (r + 1) = M - r := by omega
          rw [hsub] at h
          rw [Nat.cast_sub hrM] at h
          omega
        exact hprop (r + 1) x hx hdeep
      have hfire_prev : odoUnif d (2 * M) (r + 1) x = ((r + 1 : ℕ) : ℤ) := hearly
      obtain ⟨k, hk⟩ := hface
      have hneighValue : odoUnif d (2 * M) (r + 1) (x + unit k) = (r : ℤ) := by
        by_cases hr : r = 0
        · subst r
          have hkM : x k = (M : ℤ) := by
            rw [show M + 1 - (0 + 1) = M by omega] at hk
            exact hk
          have hout : ¬ inCube d (2 * M) (x + unit k) := by
            intro hc
            have h := (hc k).2
            rw [add_unit_self, hiCoord_two_mul, hkM] at h
            omega
          have hzero := odo_eq_zero_outside d (2 * M)
            (fun _ => 2 * (d : ℤ)) 1 (x + unit k) hout
          simpa [odoUnif] using hzero
        · have hrpos : 1 ≤ r := Nat.pos_of_ne_zero hr
          have hsub : M + 1 - (r + 1) = M - r := by omega
          rw [hsub] at hk hbelow
          have hk' : x k = ((M - r : ℕ) : ℤ) := hk
          have hsubpos : (1 : ℤ) ≤ ((M - r : ℕ) : ℤ) := by
            rw [← hk']
            exact (hx k).1
          have hrM : r ≤ M := by
            have hposNat : 1 ≤ M - r := by exact_mod_cast hsubpos
            omega
          have htarget : ((M + 1 - r : ℕ) : ℤ) =
              (M : ℤ) + 1 - (r : ℤ) := by
            have hnat : M + 1 - r = (M - r) + 1 := by omega
            rw [hnat, Nat.cast_add, Nat.cast_sub hrM]
            ring
          have hkInt : x k = (M : ℤ) - (r : ℤ) := by
            rw [hk', Nat.cast_sub hrM]
          have hbelow' : ∀ i : Fin d,
              (x + unit k) i ≤ ((M + 1 - r : ℕ) : ℤ) := by
            intro i
            by_cases hik : i = k
            · subst i
              rw [add_unit_self]
              rw [htarget, hkInt]
              omega
            · rw [add_unit_other d x k i hik]
              have hi : x i ≤ (M : ℤ) - (r : ℤ) := by
                have h := hbelow i
                rw [Nat.cast_sub hrM] at h
                exact h
              rw [htarget]
              omega
          have hface' : ∃ j : Fin d,
              (x + unit k) j = ((M + 1 - r : ℕ) : ℤ) := by
            refine ⟨k, ?_⟩
            rw [add_unit_self]
            rw [htarget, hkInt]
            omega
          have hx' : case2Pos d M (x + unit k) := by
            intro i
            by_cases hik : i = k
            · subst i
              rw [add_unit_self]
              rw [hkInt]
              constructor <;> omega
            · rw [add_unit_other d x k i hik]
              exact hx i
          have hcub : inCube d (2 * M) (x + unit k) := by
            intro i
            rw [loCoord_two_mul, hiCoord_two_mul]
            exact ⟨by have := (hx' i).1; omega, by have := (hx' i).2; omega⟩
          have hprev := ih (x + unit k) hx' hbelow' hface'
          exact hprev.2
      have hstep := case2_floor_update d M (r + 1) hd x hcube
      have hsumBound : nbrSum (odoUnif d (2 * M) (r + 1)) x ≤
          2 * (d : ℤ) * ((r + 1 : ℕ) : ℤ) - 1 := by
        unfold nbrSum
        calc
            (∑ i : Fin d,
            (odoUnif d (2 * M) (r + 1) (x + unit i) +
              odoUnif d (2 * M) (r + 1) (x - unit i)))
              ≤ ∑ i : Fin d, ((2 * ((r + 1 : ℕ) : ℤ)) -
                  (if i = k then 1 else 0)) := by
                    refine Finset.sum_le_sum ?_
                    intro i _
                    by_cases hik : i = k
                    · subst i
                      rw [hneighValue]
                      have hminus := odoUnif_le_self d (2 * M) (r + 1) (x - unit k)
                      omega
                    · have hplus := odoUnif_le_self d (2 * M) (r + 1) (x + unit i)
                      have hminus := odoUnif_le_self d (2 * M) (r + 1) (x - unit i)
                      omega
          _ = 2 * (d : ℤ) * ((r + 1 : ℕ) : ℤ) - 1 := by
                rw [Finset.sum_sub_distrib]
                have hcount : ∑ i : Fin d, (if i = k then (1 : ℤ) else 0) = 1 := by
                  simp
                rw [hcount]
                simp [Finset.sum_const, Finset.card_univ]
                ring
      have hstep' : odoUnif d (2 * M) (r + 2) x ≤ ((r + 1 : ℕ) : ℤ) := by
        rw [hstep]
        have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
          have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
          linarith
        have hlt :
            (2 * (d : ℤ) + nbrSum (odoUnif d (2 * M) (r + 1)) x) /
                (2 * (d : ℤ)) < ((r + 1 : ℕ) : ℤ) + 1 := by
          apply (Int.ediv_lt_iff_lt_mul hdpos).2
          nlinarith [hsumBound]
        omega
      have hmono := odo_mono d (2 * M) (fun _ => 2 * (d : ℤ)) (by omega : r + 1 ≤ r + 2) x
      have hmono' : odoUnif d (2 * M) (r + 1) x ≤
          odoUnif d (2 * M) (r + 1 + 1) x := by
        simpa [odoUnif, Nat.add_assoc] using hmono
      constructor
      · exact hfire_prev
      · exact le_antisymm hstep' (by rw [← hfire_prev]; exact hmono')

/-- A firing indicator for one round of the actual even-cube process. -/
def case2Fire (d M t : ℕ) (x : Site d) : ℤ :=
  odoUnif d (2 * M) (t + 1) x - odoUnif d (2 * M) t x

/-- The first nonfiring update at a positive-orthant site is indexed by
`rho(x) = M + 1 - max_i x_i`; the odometer reaches `rho(x)` and stays there
for that update. -/
theorem case2_first_wait (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (x : Site d) (hx : case2Pos d M x) :
    odoUnif d (2 * M) (case2Rho M x) x = (case2Rho M x : ℤ) ∧
      odoUnif d (2 * M) (case2Rho M x + 1) x = (case2Rho M x : ℤ) := by
  have hmax := case2_maxCoord_le hx
  have hrad : case2MaxCoord x + case2Rho M x = M + 1 := by
    dsimp [case2Rho]
    omega
  have hrad' : M + 1 - case2Rho M x = case2MaxCoord x := by omega
  have hbelow : ∀ i : Fin d, x i ≤ ((M + 1 - case2Rho M x : ℕ) : ℤ) := by
    intro i
    have hn : (x i).toNat ≤ M + 1 - case2Rho M x := by
      rw [hrad']
      exact case2_coord_le_max x i
    have hcast : ((x i).toNat : ℤ) = x i :=
      Int.toNat_of_nonneg (by have := (hx i).1; omega)
    have hn' : ((x i).toNat : ℤ) ≤ ((M + 1 - case2Rho M x : ℕ) : ℤ) := by
      exact_mod_cast hn
    rw [hcast] at hn'
    exact hn'
  obtain ⟨k, hmaxeq⟩ := case2_max_coord_attained hd x
  have hface : ∃ i : Fin d, x i = ((M + 1 - case2Rho M x : ℕ) : ℤ) := by
    refine ⟨k, ?_⟩
    have hnat : (x k).toNat = M + 1 - case2Rho M x := by omega
    have hcast : ((x k).toNat : ℤ) = x k :=
      Int.toNat_of_nonneg (by have := (hx k).1; omega)
    calc
      x k = ((x k).toNat : ℤ) := hcast.symm
      _ = ((M + 1 - case2Rho M x : ℕ) : ℤ) := by exact_mod_cast hnat
  exact case2_first_wait_layer d M (case2Rho M x) hd hM x hx hbelow hface

/-- The distance-to-exterior index for an arbitrary site, computed after
folding the even cube into its positive orthant. -/
def case2CubeRho (d M : ℕ) (x : Site d) : ℕ :=
  case2Rho M (foldPoint d (2 * M) x)

private theorem case2_fold_odo (d M t : ℕ) (x : Site d) :
    odoUnif d (2 * M) t (foldPoint d (2 * M) x) = odoUnif d (2 * M) t x := by
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) t
      (cubeSym d (2 * M) (Equiv.refl (Fin d)) (fun j => decide (1 ≤ x j)) x) =
    odo d (2 * M) (fun _ => 2 * (d : ℤ)) t x
  exact odo_cubeSym d (2 * M) (fun _ => 2 * (d : ℤ))
    (isSymmetricPile_const' d (2 * M) (2 * (d : ℤ))) t
    (Equiv.refl (Fin d)) (fun j => decide (1 ≤ x j)) x

/-- Every in-cube site first waits exactly at its graph distance from the
exterior. On the positive orthant this is `M + 1 - max_i x_i`; elsewhere the
index is computed by the cube reflection `foldPoint`. -/
theorem case2_first_wait_cube (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (x : Site d) (hx : inCube d (2 * M) x) :
    odoUnif d (2 * M) (case2CubeRho d M x) x = (case2CubeRho d M x : ℤ) ∧
      odoUnif d (2 * M) (case2CubeRho d M x + 1) x = (case2CubeRho d M x : ℤ) := by
  have hpos : case2Pos d M (foldPoint d (2 * M) x) := by
    intro i
    exact foldPoint_mem d M x hx i
  have h := case2_first_wait d M hd hM (foldPoint d (2 * M) x) hpos
  have hfold0 := case2_fold_odo d M (case2CubeRho d M x) x
  have hfold1 := case2_fold_odo d M (case2CubeRho d M x + 1) x
  constructor
  · rw [← hfold0]
    simpa [case2CubeRho] using h.1
  · rw [← hfold1]
    simpa [case2CubeRho] using h.2

private theorem case2_fire_bounds (d M t : ℕ) (x : Site d) :
    0 ≤ case2Fire d M t x ∧ case2Fire d M t x ≤ 1 := by
  simpa [case2Fire, odoUnif] using
    odo_succ_sub_bounds d (2 * M) (fun _ => 2 * (d : ℤ)) t x

private theorem case2_fire_indicator (d M t : ℕ) (x : Site d)
    (hx : inCube d (2 * M) x) :
    case2Fire d M t x =
      if 2 * (d : ℤ) ≤ sandpUnif d (2 * M) t x then 1 else 0 := by
  change odo d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) x -
      odo d (2 * M) (fun _ => 2 * (d : ℤ)) t x =
    if 2 * (d : ℤ) ≤ sandp d (2 * M) (fun _ => 2 * (d : ℤ)) t x then 1 else 0
  exact odo_succ_sub_eq d (2 * M) (fun _ => 2 * (d : ℤ)) t x hx

private theorem case2_fire_zero_outside (d M t : ℕ) (x : Site d)
    (hx : ¬ inCube d (2 * M) x) : case2Fire d M t x = 0 := by
  simp only [case2Fire, odoUnif,
    odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) x hx,
    odo_eq_zero_outside d (2 * M) (fun _ => 2 * (d : ℤ)) t x hx]
  ring

private theorem case2_fire_one_inCube {d M t : ℕ} {x : Site d}
    (hfire : case2Fire d M t x = 1) : inCube d (2 * M) x := by
  by_contra hx
  have hz := case2_fire_zero_outside d M t x hx
  omega

private theorem case2_first_wait_fire_zero (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (x : Site d) (hx : case2Pos d M x) :
    case2Fire d M (case2Rho M x) x = 0 := by
  have h := case2_first_wait d M hd hM x hx
  simp only [case2Fire]
  rw [h.1, h.2]
  omega

private theorem case2_max_step_le (d M : ℕ) (hd : 1 ≤ d) (x : Site d)
    (hx : case2Pos d M x) (i : Fin d)
    (hy : case2Pos d M (x + unit i)) :
    case2MaxCoord x ≤ case2MaxCoord (x + unit i) + 1 := by
  obtain ⟨k, hk⟩ := case2_max_coord_attained hd x
  have hcoord : (x k).toNat ≤ ((x + unit i) k).toNat + 1 := by
    by_cases hki : k = i
    · subst k
      have hxcast : ((x i).toNat : ℤ) = x i :=
        Int.toNat_of_nonneg (by have := (hx i).1; omega)
      have hycast : (((x + unit i) i).toNat : ℤ) = (x + unit i) i :=
        Int.toNat_of_nonneg (by have := (hy i).1; omega)
      have hpoint : x i ≤ (x + unit i) i := by rw [add_unit_self]; omega
      have hcast : ((x i).toNat : ℤ) ≤ (((x + unit i) i).toNat : ℤ) := by
        rw [hxcast, hycast]
        exact hpoint
      exact le_trans (by exact_mod_cast hcast) (Nat.le_add_right _ _)
    · have hpoint : (x + unit i) k = x k := add_unit_other d x i k hki
      rw [hpoint]
      omega
  calc
    case2MaxCoord x = (x k).toNat := hk.symm
    _ ≤ ((x + unit i) k).toNat + 1 := hcoord
    _ ≤ case2MaxCoord (x + unit i) + 1 := by
      exact Nat.add_le_add_right (case2_coord_le_max (x + unit i) k) 1

private theorem case2_max_step_le_sub (d M : ℕ) (hd : 1 ≤ d) (x : Site d)
    (hx : case2Pos d M x) (i : Fin d)
    (hy : case2Pos d M (x - unit i)) :
    case2MaxCoord x ≤ case2MaxCoord (x - unit i) + 1 := by
  obtain ⟨k, hk⟩ := case2_max_coord_attained hd x
  have hcoord : (x k).toNat ≤ ((x - unit i) k).toNat + 1 := by
    by_cases hki : k = i
    · subst k
      have hxcast : ((x i).toNat : ℤ) = x i :=
        Int.toNat_of_nonneg (by have := (hx i).1; omega)
      have hycast : (((x - unit i) i).toNat : ℤ) = (x - unit i) i :=
        Int.toNat_of_nonneg (by have := (hy i).1; omega)
      have hpoint : x i ≤ (x - unit i) i + 1 := by rw [sub_unit_self]; omega
      have hcast : ((x i).toNat : ℤ) ≤ (((x - unit i) i).toNat : ℤ) + 1 := by
        rw [hxcast, hycast]
        exact hpoint
      exact_mod_cast hcast
    · have hpoint : (x - unit i) k = x k := sub_unit_other d x i k hki
      rw [hpoint]
      omega
  calc
    case2MaxCoord x = (x k).toNat := hk.symm
    _ ≤ ((x - unit i) k).toNat + 1 := hcoord
    _ ≤ case2MaxCoord (x - unit i) + 1 := by
      exact Nat.add_le_add_right (case2_coord_le_max (x - unit i) k) 1

private theorem case2_rho_neighbor_le (d M : ℕ)
    (x y : Site d) (hx : case2Pos d M x) (hy : case2Pos d M y)
    (hmax : case2MaxCoord x ≤ case2MaxCoord y + 1) :
    case2Rho M y ≤ case2Rho M x + 1 := by
  have hxmax := case2_maxCoord_le hx
  have hymax := case2_maxCoord_le hy
  have hxrad : case2Rho M x + case2MaxCoord x = M + 1 := by
    dsimp [case2Rho]
    omega
  have hyrad : case2Rho M y + case2MaxCoord y = M + 1 := by
    dsimp [case2Rho]
    omega
  dsimp [case2Rho]
  omega

private theorem case2_reflect_minus_at_one (d M t : ℕ) (x : Site d) (i : Fin d)
    (hi : x i = 1) :
    odoUnif d (2 * M) t (x - unit i) = odoUnif d (2 * M) t x := by
  have heq : (fun j : Fin d =>
      if j = i then 1 - (x - unit i) i else (x - unit i) j) = x := by
    funext j
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl, sub_unit_self, hi]
      norm_num
    · rw [ite_eq_right hji, sub_unit_other d x i j hji]
  have h := odo_reflect_coord d M (2 * (d : ℤ)) t (x - unit i) i
  rw [heq] at h
  exact h.symm

private theorem case2Fire_fold_eq (d M t : ℕ) (x : Site d) :
    case2Fire d M t (foldPoint d (2 * M) x) = case2Fire d M t x := by
  simp only [case2Fire]
  rw [case2_fold_odo d M (t + 1) x, case2_fold_odo d M t x]

/-- After its first waiting update, a site cannot fire in consecutive rounds.
The sum form is equivalent to forbidding two `1` firing indicators, since each
indicator is either zero or one. -/
theorem case2_no_later_consecutive_firing (d M : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (x : Site d) (hx : case2Pos d M x) (t : ℕ)
    (ht : case2Rho M x < t) :
    case2Fire d M t x + case2Fire d M (t + 1) x ≤ 1 := by
  revert x hx ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro x hx ht
      have hrpos := case2_radius_pos hd hx
      have ht2 : 2 ≤ t := by omega
      have hfiretBound := case2_fire_bounds d M t x
      have hfireNextBound := case2_fire_bounds d M (t + 1) x
      by_contra hnot
      have hboth : case2Fire d M t x = 1 ∧ case2Fire d M (t + 1) x = 1 := by
        omega
      have hprev : case2Fire d M (t - 1) x = 0 := by
        by_cases heq : case2Rho M x = t - 1
        · rw [show t - 1 = case2Rho M x by omega]
          exact case2_first_wait_fire_zero d M hd (by omega) x hx
        · have hlt : case2Rho M x < t - 1 := by omega
          have hihRaw := ih (t - 1) (by omega) x hx hlt
          have hih : case2Fire d M (t - 1) x + case2Fire d M t x ≤ 1 := by
            simpa [show t - 1 + 1 = t by omega] using hihRaw
          have hb := case2_fire_bounds d M (t - 1) x
          omega
      have hcubex : inCube d (2 * M) x := by
        intro i
        rw [loCoord_two_mul, hiCoord_two_mul]
        exact ⟨by have := (hx i).1; omega, by have := (hx i).2; omega⟩
      have hprevlt : sandpUnif d (2 * M) (t - 1) x < 2 * (d : ℤ) := by
        have hI := case2_fire_indicator d M (t - 1) x hcubex
        rw [hprev] at hI
        by_contra hge
        rw [ite_eq_left (le_of_not_gt hge)] at hI
        omega
      have hnextge : 2 * (d : ℤ) ≤ sandpUnif d (2 * M) (t + 1) x := by
        have hI := case2_fire_indicator d M (t + 1) x hcubex
        rw [hboth.2] at hI
        by_contra hlt
        have hnot : ¬ 2 * (d : ℤ) ≤ sandpUnif d (2 * M) (t + 1) x := by omega
        rw [ite_eq_right hnot] at hI
        omega
      have hconsPrev : sandpUnif d (2 * M) t x =
          sandpUnif d (2 * M) (t - 1) x + lap (case2Fire d M (t - 1)) x := by
        have h := sandp_succ d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1) x
        have ht' : t - 1 + 1 = t := by omega
        rw [ht'] at h
        have hfire : (fun y : Site d =>
            odo d (2 * M) (fun _ => 2 * (d : ℤ)) t y -
              odo d (2 * M) (fun _ => 2 * (d : ℤ)) (t - 1) y) =
            case2Fire d M (t - 1) := by
          funext y
          simp only [case2Fire, odoUnif, ht']
        rw [hfire] at h
        simpa only [sandpUnif] using h
      have hconsNext : sandpUnif d (2 * M) (t + 1) x =
          sandpUnif d (2 * M) t x + lap (case2Fire d M t) x := by
        have h := sandp_succ d (2 * M) (fun _ => 2 * (d : ℤ)) t x
        have hfire : (fun y : Site d =>
            odo d (2 * M) (fun _ => 2 * (d : ℤ)) (t + 1) y -
              odo d (2 * M) (fun _ => 2 * (d : ℤ)) t y) = case2Fire d M t := by
          funext y
          rfl
        rw [hfire] at h
        simpa only [sandpUnif] using h
      have hcons : sandpUnif d (2 * M) (t + 1) x =
          sandpUnif d (2 * M) (t - 1) x + lap (case2Fire d M (t - 1)) x +
            lap (case2Fire d M t) x := by
        rw [hconsNext, hconsPrev]
      have hsumlarge : 2 * (d : ℤ) + 1 ≤
          nbrSum (case2Fire d M (t - 1)) x + nbrSum (case2Fire d M t) x := by
        have hcon := hcons
        unfold case2Fire at hcon
        have hprevOdo := hprev
        have hfireOdo := hboth.1
        unfold case2Fire at hprevOdo hfireOdo
        simp only [lap] at hcon
        rw [hprevOdo, hfireOdo] at hcon
        have ht' : t - 1 + 1 = t := by omega
        have hfunPrev : (fun y : Site d =>
            odoUnif d (2 * M) (t - 1 + 1) y - odoUnif d (2 * M) (t - 1) y) =
              case2Fire d M (t - 1) := by
          funext y
          simp only [case2Fire, ht']
        have hfunNow : (fun y : Site d =>
            odoUnif d (2 * M) (t + 1) y - odoUnif d (2 * M) t y) =
              case2Fire d M t := by
          funext y
          rfl
        rw [hfunPrev, hfunNow] at hcon
        have hprevUpper : sandpUnif d (2 * M) (t - 1) x ≤ 2 * (d : ℤ) - 1 := by
          omega
        linarith
      have hneighbor : ∃ i : Fin d,
          (case2Fire d M (t - 1) (x + unit i) = 1 ∧
            case2Fire d M t (x + unit i) = 1) ∨
          (case2Fire d M (t - 1) (x - unit i) = 1 ∧
            case2Fire d M t (x - unit i) = 1) := by
        by_contra hnone
        push Not at hnone
        have hsumle : nbrSum (case2Fire d M (t - 1)) x +
              nbrSum (case2Fire d M t) x ≤ 2 * (d : ℤ) := by
          unfold nbrSum
          calc
            (∑ i : Fin d,
              (case2Fire d M (t - 1) (x + unit i) +
                case2Fire d M (t - 1) (x - unit i))) +
            ∑ i : Fin d,
              (case2Fire d M t (x + unit i) + case2Fire d M t (x - unit i))
                = ∑ i : Fin d,
                    ((case2Fire d M (t - 1) (x + unit i) +
                      case2Fire d M t (x + unit i)) +
                     (case2Fire d M (t - 1) (x - unit i) +
                      case2Fire d M t (x - unit i))) := by
                        rw [← Finset.sum_add_distrib]
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ring
            _ ≤ ∑ _i : Fin d, (2 : ℤ) := by
                  refine Finset.sum_le_sum ?_
                  intro i _
                  have hplus := hnone i |>.1
                  have hminus := hnone i |>.2
                  have a := case2_fire_bounds d M (t - 1) (x + unit i)
                  have b := case2_fire_bounds d M t (x + unit i)
                  have c := case2_fire_bounds d M (t - 1) (x - unit i)
                  have e := case2_fire_bounds d M t (x - unit i)
                  omega
            _ = 2 * (d : ℤ) := by
              simp [Finset.sum_const, Finset.card_univ]
              ring
        linarith
      obtain ⟨i, hpair | hpair⟩ := hneighbor
      · have hcubey := case2_fire_one_inCube hpair.1
        have hy : case2Pos d M (x + unit i) := by
          intro j
          by_cases hji : j = i
          · subst j
            have hup := (hcubey i).2
            rw [add_unit_self, hiCoord_two_mul] at hup
            rw [add_unit_self]
            constructor
            · have := (hx i).1
              omega
            · exact hup
          · rw [add_unit_other d x i j hji]
            exact hx j
        have hmax := case2_max_step_le d M hd x hx i hy
        have hrneighbor := case2_rho_neighbor_le d M x (x + unit i) hx hy hmax
        have hrle : case2Rho M (x + unit i) ≤ t := by omega
        have hneighborNo :
            ¬ (case2Fire d M (t - 1) (x + unit i) = 1 ∧
              case2Fire d M t (x + unit i) = 1) := by
          by_cases heq : case2Rho M (x + unit i) = t
          · intro hp
            have hzero := case2_first_wait_fire_zero d M hd (by omega) _ hy
            rw [heq] at hzero
            omega
          · by_cases heq' : case2Rho M (x + unit i) = t - 1
            · intro hp
              have hzero := case2_first_wait_fire_zero d M hd (by omega) _ hy
              rw [heq'] at hzero
              omega
            · have hlt : case2Rho M (x + unit i) < t - 1 := by omega
              have hihRaw := ih (t - 1) (by omega) (x + unit i) hy hlt
              have hih : case2Fire d M (t - 1) (x + unit i) +
                  case2Fire d M t (x + unit i) ≤ 1 := by
                simpa [show t - 1 + 1 = t by omega] using hihRaw
              omega
        exact hneighborNo hpair
      · by_cases hi1 : x i = 1
        · have hpair' : case2Fire d M (t - 1) x = 1 ∧ case2Fire d M t x = 1 := by
            have hprevEq := case2_reflect_minus_at_one d M (t - 1) x i hi1
            have hnowEq := case2_reflect_minus_at_one d M t x i hi1
            have hnextEq := case2_reflect_minus_at_one d M (t + 1) x i hi1
            have hp := hpair
            unfold case2Fire at hp ⊢
            have ht' : t - 1 + 1 = t := by omega
            rw [ht'] at hp ⊢
            rw [hprevEq, hnowEq, hnextEq] at hp
            exact hp
          have hNo : case2Fire d M (t - 1) x + case2Fire d M t x ≤ 1 := by
            by_cases heq : case2Rho M x = t - 1
            · have hzero := case2_first_wait_fire_zero d M hd (by omega) x hx
              rw [heq] at hzero
              have hb := case2_fire_bounds d M t x
              omega
            · have hlt : case2Rho M x < t - 1 := by omega
              have hihRaw := ih (t - 1) (by omega) x hx hlt
              simpa [show t - 1 + 1 = t by omega] using hihRaw
          omega
        · have hy : case2Pos d M (x - unit i) := by
            intro j
            by_cases hji : j = i
            · subst j
              rw [sub_unit_self]
              have := (hx i)
              constructor <;> omega
            · rw [sub_unit_other d x i j hji]
              exact hx j
          have hmax := case2_max_step_le_sub d M hd x hx i hy
          have hrneighbor := case2_rho_neighbor_le d M x (x - unit i) hx hy hmax
          have hrle : case2Rho M (x - unit i) ≤ t := by omega
          have hneighborNo :
              ¬ (case2Fire d M (t - 1) (x - unit i) = 1 ∧
                case2Fire d M t (x - unit i) = 1) := by
            by_cases heq : case2Rho M (x - unit i) = t
            · intro hp
              have hzero := case2_first_wait_fire_zero d M hd (by omega) _ hy
              rw [heq] at hzero
              omega
            · by_cases heq' : case2Rho M (x - unit i) = t - 1
              · intro hp
                have hzero := case2_first_wait_fire_zero d M hd (by omega) _ hy
                rw [heq'] at hzero
                omega
              · have hlt : case2Rho M (x - unit i) < t - 1 := by omega
                have hihRaw := ih (t - 1) (by omega) (x - unit i) hy hlt
                have hih : case2Fire d M (t - 1) (x - unit i) +
                    case2Fire d M t (x - unit i) ≤ 1 := by
                  simpa [show t - 1 + 1 = t by omega] using hihRaw
                omega
          exact hneighborNo hpair

/-- After the first wait, no site in the even cube fires in consecutive rounds.
The first-wait index is the folded distance to the exterior. -/
theorem case2_no_later_consecutive_firing_cube (d M : ℕ) (hd : 1 ≤ d)
    (hM : 2 ≤ M) (x : Site d) (hx : inCube d (2 * M) x) (t : ℕ)
    (ht : case2CubeRho d M x < t) :
    case2Fire d M t x + case2Fire d M (t + 1) x ≤ 1 := by
  have hpos : case2Pos d M (foldPoint d (2 * M) x) := by
    intro i
    exact foldPoint_mem d M x hx i
  have hr : case2Rho M (foldPoint d (2 * M) x) < t := by
    simpa [case2CubeRho] using ht
  have h := case2_no_later_consecutive_firing d M hd hM
    (foldPoint d (2 * M) x) hpos t hr
  rw [← case2Fire_fold_eq d M t x, ← case2Fire_fold_eq d M (t + 1) x]
  exact h

end DimRed
