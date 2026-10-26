module

public import DimRed.Support.Stabilize
public import DimRed.Support.Fundamental
public import DimRed.Frozen.Prelim.ParabolicComparison

@[expose] public section

/-
The terminal odometer in dimension one and its first difference, as in
`dimred-corrected-arxiv.tex`, label `lem:one-terminal-profile`.
-/

namespace DimRed

open LatticeProb

def oneFold (x : ℤ) : ℤ := if 1 ≤ x then x else 1 - x

def onePoly (M : ℕ) (x : ℤ) : ℤ :=
  (M : ℤ) * ((M : ℤ) + 1) - x * (x - 1)

def oneProfile (M : ℕ) (y : Site 1) : ℤ :=
  if inCube 1 (2 * M) y then onePoly M (oneFold (y 0)) / 2 else 0

lemma two_dvd_mul_succ (n : ℤ) : 2 ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with hn | hn
  · exact dvd_mul_of_dvd_left hn.two_dvd _
  · rcases hn with ⟨k, hk⟩
    refine ⟨(2 * k + 1) * (k + 1), ?_⟩
    rw [hk]
    ring

lemma oneFold_reflect (x : ℤ) : oneFold (1 - x) = oneFold x := by
  by_cases hx : 1 ≤ x
  · have hx' : ¬ 1 ≤ 1 - x := by omega
    simp [oneFold, hx, hx']
  · have hx' : 1 ≤ 1 - x := by omega
    simp [oneFold, hx, hx']

lemma inCube_one_reflect (M : ℕ) (y : Site 1) :
    inCube 1 (2 * M) (fun _ => 1 - y 0) ↔ inCube 1 (2 * M) y := by
  constructor <;> intro h i
  · have hi := h i
    have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul] at hi ⊢
    change 1 - (M : ℤ) ≤ 1 - y 0 ∧ 1 - y 0 ≤ (M : ℤ) at hi
    change 1 - (M : ℤ) ≤ y 0 ∧ y 0 ≤ (M : ℤ)
    omega
  · have hi := h i
    have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul] at hi ⊢
    change 1 - (M : ℤ) ≤ y 0 ∧ y 0 ≤ (M : ℤ) at hi
    change 1 - (M : ℤ) ≤ 1 - y 0 ∧ 1 - y 0 ≤ (M : ℤ)
    omega

lemma oneProfile_reflect (M : ℕ) (y : Site 1) :
    oneProfile M (fun _ => 1 - y 0) = oneProfile M y := by
  by_cases h : inCube 1 (2 * M) y
  · have h' : inCube 1 (2 * M) (fun _ => 1 - y 0) :=
      (inCube_one_reflect M y).2 h
    rw [oneProfile, ite_eq_left h', oneProfile, ite_eq_left h]
    rw [oneFold_reflect]
  · have h' : ¬ inCube 1 (2 * M) (fun _ => 1 - y 0) :=
      fun hh => h ((inCube_one_reflect M y).1 hh)
    rw [oneProfile, ite_eq_right h', oneProfile, ite_eq_right h]

lemma oneFold_bounds (M : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y) :
    1 ≤ oneFold (y 0) ∧ oneFold (y 0) ≤ (M : ℤ) := by
  have hy0 := hy (0 : Fin 1)
  rw [loCoord_two_mul, hiCoord_two_mul] at hy0
  rw [oneFold]
  split_ifs <;> omega

lemma onePoly_nonneg (M : ℕ) {x : ℤ} (hx : 1 ≤ x) (hxM : x ≤ (M : ℤ)) :
    0 ≤ onePoly M x := by
  have h1 : 0 ≤ (M : ℤ) - x := by omega
  have h2 : 0 ≤ (M : ℤ) + x := by omega
  have h3 : 0 ≤ (M : ℤ) + x := by omega
  dsimp [onePoly]
  nlinarith [mul_nonneg h1 h2]

lemma onePoly_two_mul_ediv (M : ℕ) {x : ℤ} :
    2 * (onePoly M x / 2) = onePoly M x := by
  have hM : 2 ∣ (M : ℤ) * ((M : ℤ) + 1) := two_dvd_mul_succ (M : ℤ)
  have hx : 2 ∣ x * (x - 1) := by
    have h := two_dvd_mul_succ (x - 1)
    convert h using 1
    ring
  have h : 2 ∣ onePoly M x := by
    exact dvd_sub hM hx
  have h' := Int.ediv_mul_cancel h
  simpa [mul_comm] using h'

lemma oneProfile_nonneg (M : ℕ) (y : Site 1) : 0 ≤ oneProfile M y := by
  rw [oneProfile]
  split_ifs with hy
  · exact Int.ediv_nonneg (onePoly_nonneg M (oneFold_bounds M y hy).1
      (oneFold_bounds M y hy).2) (by norm_num)
  · rfl

lemma oneProfile_two_mul (M : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y) :
    2 * oneProfile M y = onePoly M (oneFold (y 0)) := by
  rw [oneProfile, ite_eq_left hy]
  exact onePoly_two_mul_ediv M

lemma oneProfile_lap_reflect (M : ℕ) (y : Site 1) :
    lap (oneProfile M) (fun _ => 1 - y 0) = lap (oneProfile M) y := by
  have h0 : oneProfile M (fun _ => 1 - y 0) = oneProfile M y :=
    oneProfile_reflect M y
  have hp : oneProfile M ((fun _ => 1 - y 0) + (unit (0 : Fin 1) : Site 1)) =
      oneProfile M (y - (unit (0 : Fin 1) : Site 1)) := by
    have e : (fun _ => 1 - y 0) + (unit (0 : Fin 1) : Site 1) =
        (fun _ => 1 - (y - (unit 0 : Site 1)) 0) := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [unit]
      ring
    rw [e, oneProfile_reflect]
  have hm : oneProfile M ((fun _ => 1 - y 0) - (unit (0 : Fin 1) : Site 1)) =
      oneProfile M (y + (unit (0 : Fin 1) : Site 1)) := by
    have e : (fun _ => 1 - y 0) - (unit (0 : Fin 1) : Site 1) =
        (fun _ => 1 - (y + (unit 0 : Site 1)) 0) := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [unit]
    rw [e, oneProfile_reflect]
  simp only [lap, nbrSum, Fin.sum_univ_one]
  rw [h0, hp, hm]
  ring

lemma one_coord_add (y : Site 1) :
    (y + (unit (0 : Fin 1) : Site 1)) 0 = y 0 + 1 := by
  simp [unit]

lemma one_coord_sub (y : Site 1) :
    (y - (unit (0 : Fin 1) : Site 1)) 0 = y 0 - 1 := by
  simp [unit]

lemma oneProfile_lap_pos (M : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y)
    (hpos : 1 ≤ y 0) : lap (oneProfile M) y = -1 := by
  have hy0 := hy (0 : Fin 1)
  rw [loCoord_two_mul, hiCoord_two_mul] at hy0
  have hxM : y 0 ≤ (M : ℤ) := hy0.2
  have hplus : inCube 1 (2 * M) (y + (unit (0 : Fin 1) : Site 1)) ↔
      y 0 < (M : ℤ) := by
    constructor
    · intro h
      have h' := h (0 : Fin 1)
      rw [loCoord_two_mul, hiCoord_two_mul, one_coord_add] at h'
      omega
    · intro h i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rw [loCoord_two_mul, hiCoord_two_mul, one_coord_add]
      omega
  have hminus : inCube 1 (2 * M) (y - (unit (0 : Fin 1) : Site 1)) := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul, one_coord_sub]
    omega
  have hw : 2 * oneProfile M y = onePoly M (y 0) := by
    rw [oneProfile_two_mul M y hy]
    simp [oneFold, hpos]
  have hwm : 2 * oneProfile M (y - (unit (0 : Fin 1) : Site 1)) =
      if y 0 = 1 then onePoly M (y 0) else onePoly M (y 0 - 1) := by
    rw [oneProfile_two_mul M _ hminus]
    rw [one_coord_sub]
    by_cases hx1 : y 0 = 1
    · simp [hx1, oneFold]
    · have hx2 : 1 ≤ y 0 - 1 := by omega
      simp [hx1, oneFold, hx2]
  have hwp : 2 * oneProfile M (y + (unit (0 : Fin 1) : Site 1)) =
      if y 0 < (M : ℤ) then onePoly M (y 0 + 1) else 0 := by
    by_cases hlt : y 0 < (M : ℤ)
    · rw [oneProfile_two_mul M _ (hplus.2 hlt), one_coord_add]
      have hpos' : 1 ≤ y 0 + 1 := by omega
      simp [oneFold, hpos', hlt]
    · have hout : ¬ inCube 1 (2 * M) (y + (unit (0 : Fin 1) : Site 1)) :=
        fun h => hlt (hplus.1 h)
      rw [oneProfile, ite_eq_right hout]
      simp [hlt]
  simp only [lap, nbrSum, Fin.sum_univ_one]
  norm_num only [Nat.cast_one, mul_one]
  by_cases hx1 : y 0 = 1
  · by_cases hM1 : (M : ℤ) = 1
    · norm_num [onePoly, hx1, hM1] at hw hwm hwp ⊢
      linarith
    · have hM2 : 1 < (M : ℤ) := by omega
      simp [hx1, hM2] at hwm hwp
      have hpoly : -2 * onePoly M 1 + onePoly M 2 + onePoly M 1 = -2 := by
        dsimp [onePoly]
        ring
      have hh : 2 * (-2 * oneProfile M y +
          (oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
            oneProfile M (y - (unit (0 : Fin 1) : Site 1)))) = -2 := by
        calc
          _ = -2 * (2 * oneProfile M y) +
              (2 * oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
                2 * oneProfile M (y - (unit (0 : Fin 1) : Site 1))) := by ring
          _ = -2 * onePoly M 1 + onePoly M 2 + onePoly M 1 := by
            rw [hw, hwp, hwm, hx1]
            ring
          _ = -2 := hpoly
      linarith
  · have hx2 : 1 < y 0 := by omega
    by_cases hxM' : y 0 = (M : ℤ)
    · rw [hxM', ite_eq_right (by omega : ¬ (M : ℤ) < (M : ℤ))] at hwp
      rw [hxM'] at hw
      rw [ite_eq_right hx1] at hwm
      have hpoly : -2 * onePoly M (M : ℤ) + onePoly M ((M : ℤ) - 1) = -2 := by
        dsimp [onePoly]
        ring
      have hh : 2 * (-2 * oneProfile M y +
          (oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
            oneProfile M (y - (unit (0 : Fin 1) : Site 1)))) = -2 := by
        calc
          _ = -2 * (2 * oneProfile M y) +
              (2 * oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
                2 * oneProfile M (y - (unit (0 : Fin 1) : Site 1))) := by ring
          _ = -2 * onePoly M (M : ℤ) + onePoly M ((M : ℤ) - 1) := by
            rw [hw, hwp, hwm, hxM']
            ring
          _ = -2 := hpoly
      linarith
    · have hxlt : y 0 < (M : ℤ) := by omega
      rw [ite_eq_left hxlt] at hwp
      rw [ite_eq_right hx1] at hwm
      have hpoly : -2 * onePoly M (y 0) + onePoly M (y 0 + 1) +
          onePoly M (y 0 - 1) = -2 := by
        dsimp [onePoly]
        ring
      have hh : 2 * (-2 * oneProfile M y +
          (oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
            oneProfile M (y - (unit (0 : Fin 1) : Site 1)))) = -2 := by
        calc
          _ = -2 * (2 * oneProfile M y) +
              (2 * oneProfile M (y + (unit (0 : Fin 1) : Site 1)) +
                2 * oneProfile M (y - (unit (0 : Fin 1) : Site 1))) := by ring
          _ = -2 * onePoly M (y 0) + onePoly M (y 0 + 1) +
              onePoly M (y 0 - 1) := by
            rw [hw, hwp, hwm]
            ring
          _ = -2 := hpoly
      linarith

lemma oneProfile_lap (M : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y) :
    lap (oneProfile M) y = -1 := by
  by_cases hpos : 1 ≤ y 0
  · exact oneProfile_lap_pos M y hy hpos
  · have hreflect : inCube 1 (2 * M) (fun _ => 1 - y 0) :=
      (inCube_one_reflect M y).2 hy
    rw [← oneProfile_lap_reflect M y]
    apply oneProfile_lap_pos M (fun _ => 1 - y 0) hreflect
    omega

lemma eventually_constant_of_monotone_bounded (f : ℕ → ℕ) (K : ℕ)
    (hmono : ∀ m n, m ≤ n → f m ≤ f n) (hbound : ∀ n, f n ≤ K) :
    ∃ T, ∀ n, f (T + n) = f T := by
  induction K with
  | zero =>
    refine ⟨0, ?_⟩
    intro n
    have h0 := hbound n
    have h1 := hbound 0
    have hn0 : f n = 0 := Nat.eq_zero_of_le_zero h0
    have h10 : f 0 = 0 := Nat.eq_zero_of_le_zero h1
    simpa using hn0.trans h10.symm
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
        have hn : f n ≠ K + 1 := fun h => hreach ⟨n, h⟩
        have hle := hbound n
        omega
      exact ih hbound'

lemma one_profile_comparison (M : ℕ) :
    ∀ (t : ℕ) (y : Site 1),
      odo 1 (2 * M) (fun _ => 2) t y ≤ oneProfile M y := by
  have hs1 : ∀ y, inCube 1 (2 * M) y →
      (2 : ℤ) ≤ 2 * (2 * (1 : ℤ)) - 1 := by
    intro y hy
    norm_num
  have hcomp := Frozen.parabolic_comparison 1 (2 * M) (by omega)
    (fun _ => 2) hs1
  have hu0 : ∀ (t : ℕ) (y : Site 1), 0 ≤ oneProfile M y := by
    intro t y
    exact oneProfile_nonneg M y
  have hu1 : ∀ (t : ℕ) (y : Site 1), ¬ inCube 1 (2 * M) y →
      oneProfile M y = 0 := by
    intro t y hy
    rw [oneProfile, ite_eq_right hy]
  have hcon : ∀ (t : ℕ) (y : Site 1), inCube 1 (2 * M) y →
      (-(2 : ℤ) * oneProfile M y + nbrSum (oneProfile M) y) + 2 ≤ 1 := by
    intro t y hy
    have hlap := oneProfile_lap M y hy
    rw [lap] at hlap
    norm_num at hlap ⊢
    linarith
  intro t y
  exact hcomp.2 (fun _ _ => oneProfile M _) hu0 hu1 hcon t y

lemma one_odo_eventually_constant (M : ℕ) (y : Site 1)
    (_hy : inCube 1 (2 * M) y) :
    ∃ T, ∀ n, odo 1 (2 * M) (fun _ => 2) (T + n) y =
      odo 1 (2 * M) (fun _ => 2) T y := by
  have hupper : ∀ t, odo 1 (2 * M) (fun _ => 2) t y ≤ oneProfile M y :=
    fun t => one_profile_comparison M t y
  have hboundZ : ∀ t, 0 ≤ odo 1 (2 * M) (fun _ => 2) t y :=
    fun t => odo_nonneg 1 (2 * M) (fun _ => 2) t y
  have hmonoZ : ∀ m n, m ≤ n →
      odo 1 (2 * M) (fun _ => 2) m y ≤ odo 1 (2 * M) (fun _ => 2) n y :=
    fun m n h => odo_mono 1 (2 * M) (fun _ => 2) h y
  have hbound : ∀ t,
      (odo 1 (2 * M) (fun _ => 2) t y).toNat ≤ (oneProfile M y).toNat := by
    intro t
    exact Int.toNat_le_toNat (hupper t)
  have hmono : ∀ m n, m ≤ n →
      (odo 1 (2 * M) (fun _ => 2) m y).toNat ≤
        (odo 1 (2 * M) (fun _ => 2) n y).toNat := by
    intro m n h
    exact Int.toNat_le_toNat (hmonoZ m n h)
  obtain ⟨T, hT⟩ := eventually_constant_of_monotone_bounded
    (fun t => (odo 1 (2 * M) (fun _ => 2) t y).toNat)
    (oneProfile M y).toNat hmono hbound
  refine ⟨T, ?_⟩
  intro n
  have he := congrArg (fun k : ℕ => (k : ℤ)) (hT n)
  rw [Int.toNat_of_nonneg (hboundZ (T + n)), Int.toNat_of_nonneg (hboundZ T)] at he
  exact he

lemma finset_common_stable (g : ℕ → Site 1 → ℤ) (S : Finset (Site 1))
    (hS : ∀ y ∈ S, ∃ T, ∀ n, g (T + n) y = g T y) :
    ∃ T, ∀ y ∈ S, ∀ n, g (T + n) y = g T y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp
  | @insert a S ha ih =>
    have ha' := hS a (Finset.mem_insert_self a S)
    obtain ⟨Ta, hTa⟩ := ha'
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
        _ = g (max Ta Ts) a := by
          exact (congrArg (fun k => g k a) e2).symm
    · have h1 := hTs y hy (max Ta Ts - Ts + n)
      have h2 := hTs y hy (max Ta Ts - Ts)
      have e1 : max Ta Ts + n = Ts + (max Ta Ts - Ts + n) := by omega
      have e2 : max Ta Ts = Ts + (max Ta Ts - Ts) := by omega
      calc
        g (max Ta Ts + n) y = g (Ts + (max Ta Ts - Ts + n)) y := by rw [e1]
        _ = g Ts y := h1
        _ = g (Ts + (max Ta Ts - Ts)) y := h2.symm
        _ = g (max Ta Ts) y := by
          exact (congrArg (fun k => g k y) e2).symm

lemma mem_cube_one_iff (M : ℕ) (y : Site 1) :
    y ∈ cube 1 (2 * M) ↔ inCube 1 (2 * M) y := by
  simp only [cube, Finset.mem_Icc, inCube]
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

lemma one_odo_stable (M : ℕ) :
    ∃ T, odo 1 (2 * M) (fun _ => 2) (T + 1) =
      odo 1 (2 * M) (fun _ => 2) T := by
  have hcommon := finset_common_stable
    (fun t y => odo 1 (2 * M) (fun _ => 2) t y) (cube 1 (2 * M)) (by
      intro y hy
      have hycube : inCube 1 (2 * M) y := (mem_cube_one_iff M y).1 hy
      exact one_odo_eventually_constant M y hycube)
  obtain ⟨T, hT⟩ := hcommon
  refine ⟨T, ?_⟩
  funext y
  by_cases hy : inCube 1 (2 * M) y
  · have hymem : y ∈ cube 1 (2 * M) := (mem_cube_one_iff M y).2 hy
    simpa using hT y hymem 1
  · rw [odo_eq_zero_outside 1 (2 * M) (fun _ => 2) (T + 1) y hy,
      odo_eq_zero_outside 1 (2 * M) (fun _ => 2) T y hy]

def oneSite (x : ℤ) : Site 1 := fun _ => x

lemma oneSite_add (x : ℤ) :
    oneSite x + (unit (0 : Fin 1) : Site 1) = oneSite (x + 1) := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [oneSite, unit]

lemma oneSite_sub (x : ℤ) :
    oneSite x - (unit (0 : Fin 1) : Site 1) = oneSite (x - 1) := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [oneSite, unit]

lemma one_stable_lower (M T : ℕ)
    (hstable : odo 1 (2 * M) (fun _ => 2) (T + 1) =
      odo 1 (2 * M) (fun _ => 2) T) :
    ∀ y, inCube 1 (2 * M) y →
      oneProfile M y ≤ odo 1 (2 * M) (fun _ => 2) T y := by
  let q : Site 1 → ℤ := fun y =>
    odo 1 (2 * M) (fun _ => 2) T y - oneProfile M y
  have hvlap : ∀ y, inCube 1 (2 * M) y →
      lap (odo 1 (2 * M) (fun _ => 2) T) y ≤ -1 := by
    intro y hy
    have hrec := odo_succ_eq 1 (2 * M) (fun _ => 2) T y hy
    have he := congrFun hstable y
    rw [he] at hrec
    have hn : ¬ (2 : ℤ) ≤ 2 + lap (odo 1 (2 * M) (fun _ => 2) T) y := by
      intro hc
      have hc' : 2 * ((1 : ℕ) : ℤ) ≤ sandp 1 (2 * M) (fun _ => 2) T y := by
        simpa only [sandp, Nat.cast_one, mul_one] using hc
      rw [ite_eq_left hc'] at hrec
      omega
    omega
  have hqlap : ∀ y, inCube 1 (2 * M) y → lap q y ≤ 0 := by
    intro y hy
    dsimp [q]
    rw [lap_sub]
    have hv := hvlap y hy
    have hw := oneProfile_lap M y hy
    linarith
  have hqref : ∀ y, q (fun _ => 1 - y 0) = q y := by
    intro y
    have hv := odo_cubeSym 1 (2 * M) (fun _ => 2)
      (fun _ _ _ => rfl) T
      (Equiv.refl (Fin 1)) (fun _ => false) y
    have he : cubeSym 1 (2 * M) (Equiv.refl (Fin 1)) (fun _ => false) y =
        (fun _ => 1 - y 0) := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [cubeSym, loCoord_two_mul, hiCoord_two_mul]
    rw [he] at hv
    dsimp [q]
    rw [hv, oneProfile_reflect]
  have hq01 : q (oneSite 0) = q (oneSite 1) := by
    have h := hqref (oneSite 0)
    have he : (fun _ => 1 - (oneSite 0) 0) = oneSite 1 := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [oneSite]
    rw [he] at h
    exact h.symm
  have hqboundary : q (oneSite ((M : ℤ) + 1)) = 0 := by
    have hout : ¬ inCube 1 (2 * M) (oneSite ((M : ℤ) + 1)) := by
      intro h
      have h0 := h (0 : Fin 1)
      rw [loCoord_two_mul, hiCoord_two_mul, oneSite] at h0
      omega
    dsimp [q]
    rw [odo_eq_zero_outside 1 (2 * M) (fun _ => 2) T _ hout,
      oneProfile, ite_eq_right hout]
    rfl
  have hsite_cube : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ≤ (M : ℤ) →
      inCube 1 (2 * M) (oneSite (n : ℤ)) := by
    intro n hn hnm i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul, oneSite]
    omega
  have hstep : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      q (oneSite ((n + 1 : ℕ) : ℤ)) ≤ q (oneSite (n : ℤ)) := by
    intro n hn hnm
    induction n, hn using Nat.le_induction with
    | base =>
      have h := hqlap (oneSite 1) (hsite_cube 1 (by omega) (by omega))
      simp only [lap, nbrSum, Fin.sum_univ_one] at h
      rw [oneSite_add, oneSite_sub] at h
      norm_num at h
      have hle : q (oneSite 2) ≤ q (oneSite 1) := by
        linarith [h, hq01]
      simpa using hle
    | succ n hn ih =>
      have h := hqlap (oneSite ((n + 1 : ℕ) : ℤ))
        (hsite_cube (n + 1) (by omega) (by exact_mod_cast hnm))
      simp only [lap, nbrSum, Fin.sum_univ_one] at h
      rw [oneSite_add, oneSite_sub] at h
      have eplus : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by
        push_cast
        ring
      have eminus : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by
        push_cast
        ring
      rw [eplus, eminus] at h
      norm_num at h
      have e2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by
        push_cast
        ring
      rw [← e2] at h
      have hih : q (oneSite ((n + 1 : ℕ) : ℤ)) ≤ q (oneSite (n : ℤ)) :=
        ih (by omega)
      have hle : q (oneSite ((n + 2 : ℕ) : ℤ)) ≤
          q (oneSite ((n + 1 : ℕ) : ℤ)) := by
        let a : ℤ := q (oneSite ((n + 2 : ℕ) : ℤ))
        let b : ℤ := q (oneSite ((n + 1 : ℕ) : ℤ))
        let c : ℤ := q (oneSite (n : ℤ))
        have hh : a + c ≤ 2 * b := by simpa [a, b, c] using h
        have hh' : b ≤ c := by simpa [b, c] using hih
        have hab : a ≤ b := by nlinarith [hh, hh']
        simpa [a, b, c] using hab
      simpa [Nat.add_assoc] using hle
  have hq_nonneg : ∀ n : ℕ, 1 ≤ n → n ≤ M → 0 ≤ q (oneSite (n : ℤ)) := by
    intro n hn hnm
    have hchain : ∀ k : ℕ, n ≤ k → k ≤ M + 1 →
        q (oneSite (k : ℤ)) ≤ q (oneSite (n : ℤ)) := by
      intro k hnk hk
      induction k, hnk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hnk ih =>
        have hs := hstep k (by omega) (by omega)
        exact le_trans hs (ih (by omega))
    have h := hchain (M + 1) (by omega) le_rfl
    have he : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by push_cast; ring
    rw [he, hqboundary] at h
    exact h
  intro y hy
  have hupper : odo 1 (2 * M) (fun _ => 2) T y ≤ oneProfile M y :=
    one_profile_comparison M T y
  have hqle : q y ≤ 0 := by
    dsimp [q]
    linarith
  have hqge : 0 ≤ q y := by
    by_cases hpos : 1 ≤ y 0
    · have hyM := (hy (0 : Fin 1))
      rw [loCoord_two_mul, hiCoord_two_mul] at hyM
      have he : y = oneSite (y 0) := by
        funext i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        rfl
      rw [he]
      have hy0 : 0 ≤ y 0 := by omega
      have hycast : ((y 0).toNat : ℤ) = y 0 := Int.toNat_of_nonneg hy0
      have hn1z : (1 : ℤ) ≤ ((y 0).toNat : ℤ) := by rw [hycast]; exact hpos
      have hnMz : ((y 0).toNat : ℤ) ≤ (M : ℤ) := by rw [hycast]; exact hyM.2
      have hqN := hq_nonneg (y 0).toNat (by exact_mod_cast hn1z)
        (by exact_mod_cast hnMz)
      rw [hycast] at hqN
      exact hqN
    · have hR : inCube 1 (2 * M) (fun _ => 1 - y 0) :=
        (inCube_one_reflect M y).2 hy
      have hRpos : 1 ≤ (1 - y 0) := by omega
      have hRM := hR (0 : Fin 1)
      rw [loCoord_two_mul, hiCoord_two_mul] at hRM
      have hz0 : 0 ≤ 1 - y 0 := by omega
      have hzcast : ((1 - y 0).toNat : ℤ) = 1 - y 0 := Int.toNat_of_nonneg hz0
      have hn1z : (1 : ℤ) ≤ ((1 - y 0).toNat : ℤ) := by rw [hzcast]; exact hRpos
      have hnMz : ((1 - y 0).toNat : ℤ) ≤ (M : ℤ) := by
        rw [hzcast]
        exact hRM.2
      have hqR := hq_nonneg (1 - y 0).toNat (by exact_mod_cast hn1z)
        (by exact_mod_cast hnMz)
      have he : (fun _ => 1 - y 0) = oneSite (1 - y 0) := by
        funext i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        rfl
      rw [hzcast] at hqR
      rw [← he] at hqR
      rw [hqref y] at hqR
      exact hqR
  linarith

lemma oneProfile_formula (M : ℕ) (y : Site 1) (hy : inCube 1 (2 * M) y)
    (hpos : 1 ≤ y 0) :
    oneProfile M y = onePoly M (y 0) / 2 := by
  rw [oneProfile, ite_eq_left hy]
  simp [oneFold, hpos]

theorem odoInf_one_eq (M : ℕ) (hM : 1 ≤ M) (y : Site 1)
    (hy1 : 1 ≤ y 0) (hyM : y 0 ≤ (M : ℤ)) :
    odoInfUnif 1 (2 * M) y =
      (((M : ℤ) * ((M : ℤ) + 1) - (y 0) * (y 0 - 1)) / 2).toNat := by
  have hy : inCube 1 (2 * M) y := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [loCoord_two_mul, hiCoord_two_mul]
    omega
  obtain ⟨T, hstable⟩ := one_odo_stable M
  have hu := one_profile_comparison M T y
  have hl := one_stable_lower M T hstable y hy
  have hev : odo 1 (2 * M) (fun _ => 2) T y = oneProfile M y :=
    le_antisymm hu hl
  have hi := odoInf_eq_of_stable 1 (2 * M) (fun _ => 2) T hstable y
  change odoInf 1 (2 * M) (fun _ => 2) y =
    (onePoly M (y 0) / 2).toNat
  rw [hi, hev, oneProfile_formula M y hy hy1]

theorem odoInf_one_deriv (M : ℕ) (hM : 1 ≤ M) (x : Site 1)
    (hx1 : 1 ≤ x 0) (hxM : x 0 < (M : ℤ)) :
    ((odoInfUnif 1 (2 * M) x).toNat : ℤ) -
        ((odoInfUnif 1 (2 * M) (x + (unit (0 : Fin 1) : Site 1))).toNat : ℤ) = x 0 := by
  have hxM' : x 0 + 1 ≤ (M : ℤ) := by omega
  have heq1 := odoInf_one_eq M hM x hx1 (by omega)
  have hplus1 : 1 ≤ (x + (unit (0 : Fin 1) : Site 1)) 0 := by
    rw [one_coord_add]
    omega
  have hplusM : (x + (unit (0 : Fin 1) : Site 1)) 0 ≤ (M : ℤ) := by
    rw [one_coord_add]
    exact hxM'
  have heq2 := odoInf_one_eq M hM (x + (unit (0 : Fin 1) : Site 1))
    hplus1 hplusM
  rw [one_coord_add] at heq2
  have h1nat := congrArg ENat.toNat heq1
  have h2nat := congrArg ENat.toNat heq2
  simp only [ENat.toNat_natCast] at h1nat h2nat
  have h1 := congrArg (fun n : ℕ => (n : ℤ)) h1nat
  have h2 := congrArg (fun n : ℕ => (n : ℤ)) h2nat
  have hpoly1 := onePoly_two_mul_ediv (M := M) (x := x 0)
  have hpoly2 := onePoly_two_mul_ediv (M := M) (x := x 0 + 1)
  have hnonneg1 : 0 ≤ onePoly M (x 0) / 2 :=
    Int.ediv_nonneg (onePoly_nonneg M hx1 (by omega)) (by norm_num)
  have hnonneg2 : 0 ≤ onePoly M (x 0 + 1) / 2 :=
    Int.ediv_nonneg (onePoly_nonneg M (by omega) hxM') (by norm_num)
  have hcast1 : ((onePoly M (x 0) / 2).toNat : ℤ) = onePoly M (x 0) / 2 :=
    Int.toNat_of_nonneg hnonneg1
  have hcast2 : ((onePoly M (x 0 + 1) / 2).toNat : ℤ) =
      onePoly M (x 0 + 1) / 2 := Int.toNat_of_nonneg hnonneg2
  have hcast1' :
      ((((M : ℤ) * ((M : ℤ) + 1) - (x 0) * (x 0 - 1)) / 2).toNat : ℤ) =
        ((M : ℤ) * ((M : ℤ) + 1) - (x 0) * (x 0 - 1)) / 2 := by
    simpa [onePoly] using hcast1
  have hcast2' :
      ((((M : ℤ) * ((M : ℤ) + 1) - (x 0 + 1) * (x 0 + 1 - 1)) / 2).toNat : ℤ) =
        ((M : ℤ) * ((M : ℤ) + 1) - (x 0 + 1) * (x 0 + 1 - 1)) / 2 := by
    simpa [onePoly] using hcast2
  rw [hcast1'] at h1
  rw [hcast2'] at h2
  rw [h1, h2]
  have hpolyDiff : onePoly M (x 0) - onePoly M (x 0 + 1) = 2 * x 0 := by
    dsimp [onePoly]
    ring
  have hdiff : onePoly M (x 0) / 2 - onePoly M (x 0 + 1) / 2 = x 0 := by
    nlinarith [hpoly1, hpoly2, hpolyDiff]
  exact hdiff
