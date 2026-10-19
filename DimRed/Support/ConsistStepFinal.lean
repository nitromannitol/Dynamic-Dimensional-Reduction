/-
The self-similarity step of the joint induction, `dimred-corrected-arxiv.tex`.

`consist_step_of_earlier` discharges the `hconsist_step` hypothesis of
`reg_induction`.  In dimension one it is `odo_one_consist_all`.  In dimension
`e + 1 ≥ 2` the clause at `(M, j)` is one step from `M` to `M - 1`
(`consist_onestep_top`) followed by the clause at `(M - 1, j)`.  The time bound
`t ≤ τ_j ≤ τ_{M-1}` comes from the dimension independence of the topple time
(`toppleTime_dim_eq`) and its scale monotonicity in dimension one.  The one step
at time `s + 1` compares neighbour sums at time `s`: coordinates above two fold
into the simplex, and a coordinate equal to two uses the reflecting-boundary
identity `odo_gap_zero`, which is dimensional reduction at scales `M` and
`M - 1` plus the one-step identity in dimension `e`.
-/
import DimRed.Support.NbrSumSelfSim
import DimRed.Support.ReflectShift
import DimRed.Support.OneStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace DimRed

open LatticeProb

/-- The one-dimensional corner of the side-`b` cube, shifted down to scale `a`,
is the corner of the side-`a` cube. -/
theorem cornerPoint_one_shift (a b : ℕ) :
    (fun i => cornerPoint 1 b i - ((b : ℤ) - (a : ℤ))) = (cornerPoint 1 a : Site 1) := by
  funext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst hi
  rw [cornerPoint, cornerPoint]
  simp

/-- The one-dimensional corner lies in the simplex. -/
theorem cornerPoint_one_inSimplex (b : ℕ) (hb : 1 ≤ b) : inSimplex 1 b (cornerPoint 1 b) :=
  cornerPoint_mem_inSimplex 1 b hb

/-- The one-dimensional topple time is monotone in the scale, given the
self-similarity clause at the larger scale at every time. -/
theorem toppleTime_one_mono (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hC : 2 ≤ b → ∀ n : ℕ, RegConsist 1 b n) :
    toppleTime 1 a ≤ toppleTime 1 b := by
  by_cases hb2 : 2 ≤ b
  · refine toppleTime_mono_scale a b ha hab ?_ ?_ ?_
    · intro n hn
      have hc := hC hb2 n a ha hab hn (cornerPoint 1 b)
        (cornerPoint_one_inSimplex b (by omega))
        (fun i => by
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          rw [cornerPoint]
          simp
          omega)
      rw [cornerPoint_one_shift a b] at hc
      exact hc
    · exact corner_reaches 1 b (by norm_num) (by omega)
        (fun e he hel => absurd hel (by omega))
    · exact corner_reaches 1 a (by norm_num) ha
        (fun e he hel => absurd hel (by omega))
  · have hb1 : b = 1 := by omega
    subst hb1
    have ha1 : a = 1 := by omega
    subst ha1
    exact le_rfl

/-- The self-similarity step in dimension one. -/
theorem consist_step_dim_one (M t : ℕ) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier 1 M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    RegConsist 1 M t := by
  intro j hj1 hjM ht x hx hxgt
  have hmono : ∀ {a b : ℕ}, j ≤ a → a ≤ b → b < M → toppleTime 1 a ≤ toppleTime 1 b :=
    fun {a b} ha hab hbM => toppleTime_one_mono a b (by omega) hab
      (fun hb2 n => (hprior 1 b n (Or.inr (Or.inl ⟨rfl, hbM⟩)) le_rfl hb2).1.1)
  refine odo_one_consist_all M j t hM hj1 hjM ht hmono ?_ ?_ x hx (hxgt 0)
  · intro K hK hKMb t' ht' z hz1 hzK
    have h := (hprior 1 K t' (by
        rcases lt_or_eq_of_le hKMb with hKM' | hKM'
        · exact Or.inr (Or.inl ⟨rfl, hKM'⟩)
        · exact Or.inr (Or.inr ⟨rfl, hKM', by omega⟩))
      le_rfl (by omega)).1.1
    have hz' : (fun i : Fin 1 => z i - ((K : ℤ) - ((K - 1 : ℕ) : ℤ))) =
        (fun _ : Fin 1 => z 0 - 1) := by
      funext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [Nat.cast_sub (by omega : 1 ≤ K)]
      norm_num
    have hmain := h (K - 1) (by omega) (by omega)
      (toppleTime_le_of_lt_of_le (j := j) (K := K) (M := M) (t := t) (t' := t')
        hmono hK hKMb (by omega) ht ht')
      z (by
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          exact ⟨by omega, hzK⟩
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj])
      (fun i => by
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst hi
        change ((K : ℤ) - ((K - 1 : ℕ) : ℤ)) < z 0
        rw [Nat.cast_sub (by omega : 1 ≤ K)]
        norm_num
        omega)
    rw [hz'] at hmain
    exact hmain
  · intro K hK hKMb s hs hreg hz
    by_cases hK1 : K - 1 = 1
    · -- scale one: the regime hypothesis is impossible
      exfalso
      have htau : toppleTime (0 + 1 + 0) (K - 1) = 1 := by
        rw [show (0 + 1 + 0 : ℕ) = 1 by norm_num, hK1, toppleTime_one_one]
      rw [htau] at hreg
      have hle : (1 : ℕ∞) ≤ ((s + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : 1 ≤ s + 1)
      exact absurd hreg (not_lt.mpr hle)
    · have h := (hprior 1 (K - 1) s (Or.inr (Or.inl ⟨rfl, by omega⟩))
        le_rfl (by omega)).1.2.2.2.1
      have hreg' : ((s : ℕ∞) < toppleTime (0 + 1 + 0) (K - 1) ∨
          1 ≤ 0 ∧ toppleTime (0 + 1 + 0) (K - 1) ≤ (s : ℕ∞)) := by
        left
        have h2 : (s : ℕ∞) < ((s + 1 : ℕ) : ℕ∞) := by
          rw [Nat.cast_lt]; omega
        exact lt_of_lt_of_le h2 (le_of_lt hreg)
      have htopp : odoUnif (0 + 1 + 0) (2 * (K - 1)) s
          (facetPoint (fun _ : Fin 0 => (1 : ℤ)) 1 0) =
          odoUnif (0 + 1 + 0) (2 * (K - 1)) s
            (facetPoint (fun _ : Fin 0 => (1 : ℤ)) 2 0) + 1 := by
        rw [facetPoint_zero_head', facetPoint_zero_head']
        simp only [Fin.eq_zero, if_true]
        exact hz
      have hx2 : ∀ a : Fin 0, 2 ≤ (fun _ : Fin 0 => (1 : ℤ)) a :=
        fun a => absurd a.2 (by omega)
      have hsimp : inSimplex (0 + 1 + 0) (K - 1)
          (facetPoint (fun _ : Fin 0 => (1 : ℤ)) 1 0) := by
        rw [facetPoint_zero_head']
        constructor
        · intro i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst hi
          simp only [Fin.eq_zero, if_true]
          omega
        · intro i j _
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          have hj : j = (0 : Fin 1) := Fin.eq_zero j
          rw [hi, hj]
      have hres := h 0 0 rfl (fun _ : Fin 0 => (1 : ℤ)) hx2 hsimp hreg' htopp
      rw [facetPoint_zero_head', facetPoint_zero_head'] at hres
      simp only [Fin.eq_zero, if_true] at hres
      exact hres

/-- The reflecting-boundary identity `eq:reflecting_boundaries`,
`dimred-corrected-arxiv.tex:995-1008`: at a coordinate equal to two, the odometer does not see
the step down to one.  Dimensional reduction at both scales and the one-step
self-similarity in dimensions `e` and `e + 1` identify both values with the
odometer of the smaller cube in dimension `e`. -/
theorem odo_gap_zero (e m s : ℕ) (he : 1 ≤ e) (hm : 2 ≤ m)
    (hred : DimRedAt (e + 1) m s) (hred' : DimRedAt (e + 1) (m - 1) s)
    (hlow : ∀ x : Site e, inSimplex e m x → (∀ i, 1 < x i) →
      odoUnif e (2 * m) s x = odoUnif e (2 * (m - 1)) s (fun i => x i - 1))
    (y : Site (e + 1)) (hy : inSimplex (e + 1) m y) (hygt : ∀ i, 1 < y i)
    (hself : odoUnif (e + 1) (2 * m) s y =
      odoUnif (e + 1) (2 * (m - 1)) s (fun i => y i - 1))
    (k : Fin (e + 1)) (hk : y k = 2) :
    odoUnif (e + 1) (2 * m) s (y - unit k) = odoUnif (e + 1) (2 * m) s y := by
  have hlast : y (Fin.last e) = 2 := by
    have h1 := hy.2 k (Fin.last e) (Fin.le_last k)
    have h2 := hygt (Fin.last e)
    omega
  have hswap : (fun i => (y - unit k) (Equiv.swap k (Fin.last e) i))
      = y - unit (Fin.last e) := by
    funext i
    rw [sub_unit_apply, sub_unit_apply, Equiv.swap_apply_def]
    by_cases hik : i = k
    · subst hik
      by_cases hkl : i = Fin.last e
      · subst hkl; simp
      · simp only [if_true, if_neg hkl, if_neg (Ne.symm hkl)]
        omega
    · by_cases hil : i = Fin.last e
      · subst hil
        simp only [if_neg hik, if_true]
        omega
      · simp only [if_neg hik, if_neg hil]
  have h1 : odoUnif (e + 1) (2 * m) s (y - unit k)
      = odoUnif (e + 1) (2 * m) s (y - unit (Fin.last e)) := by
    rw [← hswap]
    simp only [odoUnif]
    exact (odo_swap_coord (e + 1) m _ s (y - unit k) k (Fin.last e)).symm
  set x : Site e := Fin.init y with hxdef
  have hxi : ∀ i : Fin e, x i = y (Fin.castSucc i) := fun i => rfl
  have hy_eq : y - unit (Fin.last e) = Fin.snoc x 1 := by
    funext i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [sub_unit_self, Fin.snoc_last, hlast]
      norm_num
    · rw [sub_unit_other _ _ _ _ (Fin.castSucc_ne_last a), Fin.snoc_castSucc, hxi]
  have hy1 : (fun i => y i - 1) = Fin.snoc (fun i => x i - 1) (1 : ℤ) := by
    funext i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, hlast]
      norm_num
    · rw [Fin.snoc_castSucc, hxi]
  have hxgt : ∀ i, 1 < x i := fun i => by rw [hxi]; exact hygt _
  have hx : inSimplex e m x := by
    constructor
    · intro i
      rw [hxi]
      exact hy.1 _
    · intro i l hil
      rw [hxi, hxi]
      exact hy.2 _ _ (Fin.castSucc_le_castSucc_iff.mpr hil)
  have hx1 : inSimplex e (m - 1) (fun i => x i - 1) := by
    have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    constructor
    · intro i
      have h1 := hx.1 i
      have h2 := hxgt i
      rw [hcast]
      show 1 ≤ x i - 1 ∧ x i - 1 ≤ (m : ℤ) - 1
      constructor <;> omega
    · intro i l hil
      have h := hx.2 i l hil
      simp only
      omega
  rw [h1, hy_eq, hred e he rfl x hx, hlow x hx hxgt, ← hred' e he rfl _ hx1, ← hy1,
    ← hself]

/-- The neighbour-sum identity of the one-step self-similarity at a point of
`S_m` with every coordinate above one, `dimred-corrected-arxiv.tex:1021-1082`: coordinates above
two are handled by the fold as in `nbrSum_selfsim_step`, and coordinates equal
to two by the reflecting-boundary identity `hgap`. -/
theorem nbrSum_selfsim_gen (d m t : ℕ) (hm : 2 ≤ m)
    (y : Site d) (hy : inSimplex d m y) (hygt : ∀ i : Fin d, 1 < y i)
    (hstep : ∀ z : Site d, inSimplex d m z → (∀ i : Fin d, 1 < z i) →
      odoUnif d (2 * m) t z = odoUnif d (2 * (m - 1)) t (fun i => z i - 1))
    (hgap : ∀ k : Fin d, y k = 2 →
      odoUnif d (2 * m) t (y - unit k) = odoUnif d (2 * m) t y) :
    nbrSum (odoUnif d (2 * m) t) y
      = nbrSum (odoUnif d (2 * (m - 1)) t) (fun i => y i - 1) := by
  have hfold : ∀ z : Site d, inCube d (2 * m) z → (∀ k, 2 ≤ z k) →
      inSimplex d m (toSimplexPoint d m z) ∧
        (∀ k : Fin d, 1 < toSimplexPoint d m z k) := by
    intro z hz hz2
    refine ⟨inSimplex_toSimplexPoint d m z hz, fun k => ?_⟩
    rw [toSimplexPoint]
    have hfold2 : 2 ≤ foldPoint d (2 * m) z
        (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k) := by
      rw [foldPoint_apply, if_pos (by
        have := hz2 (Tuple.sort (fun i => -(foldPoint d (2 * m) z i)) k); omega)]
      exact hz2 _
    exact hfold2
  have hviaFold : ∀ z : Site d, inCube d (2 * m) z → (∀ k, 2 ≤ z k) →
      odoUnif d (2 * m) t z = odoUnif d (2 * (m - 1)) t (fun k => z k - 1) := by
    intro z hz hz2
    obtain ⟨hf, hg⟩ := hfold z hz hz2
    rw [← odoUnif_toSimplexPoint d m t z, hstep _ hf hg,
      odoUnif_toSimplexPoint_sub d m t z (fun k => by have := hz2 k; omega)]
  have hplus : ∀ i : Fin d, odoUnif d (2 * m) t (y + unit i)
      = odoUnif d (2 * (m - 1)) t (fun k => (y + unit i) k - 1) := by
    intro i
    by_cases hlt : y i < (m : ℤ)
    · refine hviaFold _ (fun k => ?_) (fun k => ?_)
      · have h1 := hy.1 k
        rw [loCoord_two_mul, hiCoord_two_mul]
        by_cases hk : k = i
        · subst hk
          rw [add_unit_self]
          constructor <;> omega
        · rw [add_unit_other _ _ _ _ hk]
          constructor <;> omega
      · have h2 := hygt k
        by_cases hk : k = i
        · subst hk
          rw [add_unit_self]
          omega
        · rw [add_unit_other _ _ _ _ hk]
          omega
    · have hyi : y i = (m : ℤ) := by
        have h1 := hy.1 i
        omega
      have hout : odoUnif d (2 * m) t (y + unit i) = 0 := by
        rw [odoUnif, odo_eq_zero_outside]
        intro hc
        have h1 := hc i
        rw [loCoord_two_mul, hiCoord_two_mul, add_unit_self, hyi] at h1
        omega
      have hout' : odoUnif d (2 * (m - 1)) t (fun k => (y + unit i) k - 1) = 0 := by
        rw [odoUnif, odo_eq_zero_outside]
        intro hc
        have h1 := hc i
        rw [loCoord_two_mul, hiCoord_two_mul] at h1
        simp only at h1
        rw [add_unit_self, hyi] at h1
        omega
      rw [hout, hout']
  have hminus : ∀ i : Fin d, odoUnif d (2 * m) t (y - unit i)
      = odoUnif d (2 * (m - 1)) t (fun k => (y - unit i) k - 1) := by
    intro i
    by_cases h2 : y i = 2
    · rw [hgap i h2, odoUnif_sub_unit_shift_eq d m t y i h2]
      exact hstep y hy hygt
    · refine hviaFold _ (fun k => ?_) (fun k => ?_)
      · have h1 := hy.1 k
        have h3 := hygt k
        rw [loCoord_two_mul, hiCoord_two_mul]
        by_cases hk : k = i
        · subst hk
          rw [sub_unit_self]
          constructor <;> omega
        · rw [sub_unit_other _ _ _ _ hk]
          constructor <;> omega
      · have h3 := hygt k
        by_cases hk : k = i
        · subst hk
          rw [sub_unit_self]
          omega
        · rw [sub_unit_other _ _ _ _ hk]
          omega
  simp only [nbrSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hplus i, hminus i]
  congr 1 <;> (congr 1; funext k; simp only [Pi.add_apply, Pi.sub_apply]; ring)

/-- One step of the recursion carries the one-step self-similarity at a point
from time `s` to time `s + 1`, given the neighbour-sum identity at time `s`. -/
theorem onestep_succ (d m s : ℕ) (hm : 2 ≤ m)
    (y : Site d) (hy : inSimplex d m y) (hygt : ∀ i : Fin d, 1 < y i)
    (hself : odoUnif d (2 * m) s y = odoUnif d (2 * (m - 1)) s (fun i => y i - 1))
    (hnbr : nbrSum (odoUnif d (2 * m) s) y
      = nbrSum (odoUnif d (2 * (m - 1)) s) (fun i => y i - 1)) :
    odoUnif d (2 * m) (s + 1) y = odoUnif d (2 * (m - 1)) (s + 1) (fun i => y i - 1) := by
  have hyc : inCube d (2 * m) y := inCube_of_inSimplex_gt_one d m y hm hy hygt
  have hy1c : inCube d (2 * (m - 1)) (fun i => y i - 1) :=
    inCube_sub_one_of_gt_one d m y hm (fun k => (hy.1 k).1) (fun k => (hy.1 k).2) hygt
  have hs : sandp d (2 * m) (fun _ => 2 * (d : ℤ)) s y
      = sandp d (2 * (m - 1)) (fun _ => 2 * (d : ℤ)) s (fun i => y i - 1) := by
    change 2 * (d : ℤ) + (-(2 * (d : ℤ)) * odoUnif d (2 * m) s y
        + nbrSum (odoUnif d (2 * m) s) y)
      = 2 * (d : ℤ) + (-(2 * (d : ℤ)) * odoUnif d (2 * (m - 1)) s (fun i => y i - 1)
        + nbrSum (odoUnif d (2 * (m - 1)) s) (fun i => y i - 1))
    rw [hself, hnbr]
  have hself' : odo d (2 * m) (fun _ => 2 * (d : ℤ)) s y
      = odo d (2 * (m - 1)) (fun _ => 2 * (d : ℤ)) s (fun i => y i - 1) := hself
  show odo d (2 * m) (fun _ => 2 * (d : ℤ)) (s + 1) y
    = odo d (2 * (m - 1)) (fun _ => 2 * (d : ℤ)) (s + 1) (fun i => y i - 1)
  rw [odo_succ_eq d (2 * m) (fun _ => 2 * (d : ℤ)) s y hyc,
    odo_succ_eq d (2 * (m - 1)) (fun _ => 2 * (d : ℤ)) s (fun i => y i - 1) hy1c, hs, hself']

/-- The topple time at scale `a` does not depend on the dimension, given
dimensional reduction at scale `a` in every dimension below `D + 1`. -/
theorem toppleTime_dim_eq (a D : ℕ) (ha : 1 ≤ a)
    (hred : ∀ e : ℕ, 1 ≤ e → e < D → ∀ (t : ℕ) (y : Site e), inSimplex e a y →
      odoUnif (e + 1) (2 * a) t (Fin.snoc y 1) = odoUnif e (2 * a) t y) :
    ∀ e : ℕ, 1 ≤ e → e ≤ D → toppleTime e a = toppleTime 1 a := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => intro _; rfl
  | succ e he ih =>
    intro heD
    rw [← ih (by omega)]
    exact le_antisymm
      (toppleTime_mono_dim_le e a he ha (hred e he (by omega))
        (fun e' he' hlt => hred e' he' (by omega)))
      (toppleTime_mono_dim e a he ha (hred e he (by omega))
        (fun e' he' hlt => hred e' he' (by omega)))

/-- The one-step self-similarity at the top scale `M`, `eq:self_sim1`, for
`t ≤ τ_{M-1}` in dimensions `e + 1` and `e`. -/
theorem consist_onestep_top (e M t : ℕ) (he : 1 ≤ e) (hM : 3 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier (e + 1) M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (ht : (t : ℕ∞) ≤ toppleTime (e + 1) (M - 1))
    (ht' : (t : ℕ∞) ≤ toppleTime e (M - 1))
    (y : Site (e + 1)) (hy : inSimplex (e + 1) M y) (hygt : ∀ i, 1 < y i) :
    odoUnif (e + 1) (2 * M) t y = odoUnif (e + 1) (2 * (M - 1)) t (fun i => y i - 1) := by
  have hshift : (M : ℤ) - ((M - 1 : ℕ) : ℤ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    ring
  cases t with
  | zero => rfl
  | succ s =>
    have hs : (s : ℕ∞) ≤ toppleTime (e + 1) (M - 1) :=
      le_trans (by exact_mod_cast Nat.le_succ s) ht
    have hs' : (s : ℕ∞) ≤ toppleTime e (M - 1) :=
      le_trans (by exact_mod_cast Nat.le_succ s) ht'
    -- the one-step identity at time `s` in dimension `e + 1`
    have hstep : ∀ z : Site (e + 1), inSimplex (e + 1) M z → (∀ i, 1 < z i) →
        odoUnif (e + 1) (2 * M) s z
          = odoUnif (e + 1) (2 * (M - 1)) s (fun i => z i - 1) := by
      intro z hz hzgt
      have hC := (hprior (e + 1) M s (Or.inr (Or.inr ⟨rfl, rfl, by omega⟩))
        (by omega) (by omega)).1.1
      have h := hC (M - 1) (by omega) (by omega) hs z hz (fun i => by
        rw [hshift]; exact hzgt i)
      rw [hshift] at h
      exact h
    -- the one-step identity at time `s` in dimension `e`
    have hlow : ∀ x : Site e, inSimplex e M x → (∀ i, 1 < x i) →
        odoUnif e (2 * M) s x = odoUnif e (2 * (M - 1)) s (fun i => x i - 1) := by
      intro x hx hxgt
      have hC := (hprior e M s (Or.inl (by omega)) he (by omega)).1.1
      have h := hC (M - 1) (by omega) (by omega) hs' x hx (fun i => by
        rw [hshift]; exact hxgt i)
      rw [hshift] at h
      exact h
    have hred : DimRedAt (e + 1) M s :=
      (hprior (e + 1) M s (Or.inr (Or.inr ⟨rfl, rfl, by omega⟩)) (by omega) (by omega)).2
    have hred' : DimRedAt (e + 1) (M - 1) s :=
      (hprior (e + 1) (M - 1) s (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega) (by omega)).2
    have hgap : ∀ k : Fin (e + 1), y k = 2 →
        odoUnif (e + 1) (2 * M) s (y - unit k) = odoUnif (e + 1) (2 * M) s y :=
      fun k hk => odo_gap_zero e M s he (by omega) hred hred' hlow y hy hygt
        (hstep y hy hygt) k hk
    exact onestep_succ (e + 1) M s (by omega) y hy hygt (hstep y hy hygt)
      (nbrSum_selfsim_gen (e + 1) M s (by omega) y hy hygt hstep hgap)

/-- The self-similarity step in dimension at least two. -/
theorem consist_step_ge_two (e M t : ℕ) (he : 1 ≤ e) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier (e + 1) M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t') :
    RegConsist (e + 1) M t := by
  intro j hj1 hjM ht x hx hxgt
  rcases Nat.eq_or_lt_of_le hjM with hjM' | hjM'
  · subst hjM'
    simp
  have hxgt1 : ∀ i, 1 < x i := fun i => by have := hxgt i; omega
  by_cases hM2 : M = 2
  · -- scale two: `j = 1`, so `t ≤ 1`
    subst hM2
    have hj : j = 1 := by omega
    subst hj
    rw [toppleTime_one_eq_one (e + 1) (by omega)] at ht
    have ht1 : t ≤ 1 := by exact_mod_cast ht
    have hshift : (fun i => x i - (((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))) = fun i => x i - 1 := by
      funext i; norm_num
    rw [hshift]
    rcases Nat.lt_or_ge t 1 with ht0 | ht1'
    · have : t = 0 := by omega
      subst this
      rfl
    · have : t = 1 := by omega
      subst this
      rw [odoUnif_one_eq_one (e + 1) 2 x (inCube_of_inSimplex_gt_one (e + 1) 2 x le_rfl hx hxgt1),
        odoUnif_one_eq_one (e + 1) 1 _
          (inCube_sub_one_of_gt_one (e + 1) 2 x le_rfl (fun k => (hx.1 k).1)
            (fun k => (hx.1 k).2) hxgt1)]
  have hM3 : 3 ≤ M := by omega
  -- dimensional reduction at every scale below `M`, in every dimension up to `e + 1`
  have hredAll : ∀ a : ℕ, 2 ≤ a → a < M → ∀ e' : ℕ, 1 ≤ e' → e' < e + 1 →
      ∀ (t' : ℕ) (y : Site e'), inSimplex e' a y →
      odoUnif (e' + 1) (2 * a) t' (Fin.snoc y 1) = odoUnif e' (2 * a) t' y := by
    intro a ha2 haM e' he' hlt t' y hy
    have hE : regEarlier (e + 1) M t (e' + 1) a t' := by
      rcases Nat.lt_or_ge (e' + 1) (e + 1) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, haM⟩)
    exact (hprior (e' + 1) a t' hE (by omega) ha2).2 e' he' rfl y hy
  have hdimeq : ∀ a : ℕ, 2 ≤ a → a < M → ∀ e' : ℕ, 1 ≤ e' → e' ≤ e + 1 →
      toppleTime e' a = toppleTime 1 a :=
    fun a ha2 haM => toppleTime_dim_eq a (e + 1) (by omega) (hredAll a ha2 haM)
  -- the topple time is monotone in the scale below `M`
  have hmono : toppleTime (e + 1) j ≤ toppleTime (e + 1) (M - 1) := by
    by_cases hj2 : 2 ≤ j
    · rw [hdimeq j hj2 hjM' (e + 1) (by omega) le_rfl,
        hdimeq (M - 1) (by omega) (by omega) (e + 1) (by omega) le_rfl]
      exact toppleTime_one_mono j (M - 1) hj1 (by omega)
        (fun hb2 n => (hprior 1 (M - 1) n (Or.inl (by omega)) le_rfl hb2).1.1)
    · have hj : j = 1 := by omega
      subst hj
      rw [toppleTime_one_eq_one (e + 1) (by omega)]
      exact one_le_toppleTime _ _
  have htop : (t : ℕ∞) ≤ toppleTime (e + 1) (M - 1) := le_trans ht hmono
  have htop' : (t : ℕ∞) ≤ toppleTime e (M - 1) := by
    rw [hdimeq (M - 1) (by omega) (by omega) e he (by omega)]
    rw [hdimeq (M - 1) (by omega) (by omega) (e + 1) (by omega) le_rfl] at htop
    exact htop
  -- one step down from `M` to `M - 1`, then the clause at `M - 1`
  have h1 := consist_onestep_top e M t he hM3 hprior htop htop' x hx hxgt1
  have hC := (hprior (e + 1) (M - 1) t (Or.inr (Or.inl ⟨rfl, by omega⟩))
    (by omega) (by omega)).1.1
  have hx1 : inSimplex (e + 1) (M - 1) (fun i => x i - 1) := by
    have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      norm_num
    constructor
    · intro i
      have h1 := hx.1 i
      have h2 := hxgt1 i
      rw [hcast]
      show 1 ≤ x i - 1 ∧ x i - 1 ≤ (M : ℤ) - 1
      constructor <;> omega
    · intro i l hil
      have h := hx.2 i l hil
      show x l - 1 ≤ x i - 1
      omega
  have h2 := hC j hj1 (by omega) ht (fun i => x i - 1) hx1 (fun i => by
    have := hxgt i
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    show (M : ℤ) - (1 : ℕ) - (j : ℤ) < x i - 1
    push_cast
    omega)
  rw [h1, h2]
  congr 1
  funext i
  rw [Nat.cast_sub (by omega : 1 ≤ M)]
  push_cast
  ring

/-- The self-similarity clause at one triple, `dimred-corrected-arxiv.tex:726-729`, from the
earlier instances of the joint induction. -/
theorem consist_step_of_earlier (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (_hdimred : DimRedAt d M t) (_hfacet : RegStrongFacet d M t) :
    RegConsist d M t := by
  rcases Nat.eq_or_lt_of_le hd with hd1 | hd2
  · subst hd1
    exact consist_step_dim_one M t hM hprior
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    exact consist_step_ge_two e M t (by omega) hM hprior

end DimRed
