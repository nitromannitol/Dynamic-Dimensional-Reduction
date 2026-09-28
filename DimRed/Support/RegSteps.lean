import DimRed.Support.RegBridges
import DimRed.Support.SimplexFold

/-!
# Dimensional reduction at one triple

Dimensional reduction at one triple, `dimred.tex:1129-1182`.

The step is `odo_dimred_step`, whose remaining input is the unit-gap interior
branch `odo_dimred_critical`.  Both are stated for the raw point `x` of the
sorted domain; the reduction identity `DimRedAt` is stated for `Fin.snoc x 1`,
which is the same point.

The earlier instances enter through the bridges of `DimRed.Support.RegBridges`:
the facet steps at time `t - 1` come from the clauses at the earlier time
`t - 1` of the same `(d, M)`, and the lower-dimensional steps from the clauses
at dimension `i < d`.  A raw point of the cube is carried into the sorted domain
by `toSimplexPoint` without changing the odometer (`DimRed.Support.SimplexFold`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the induction over the earlier instances unfolds the whole regularity tuple
-- at each step, which needs the extra budget
set_option maxHeartbeats 800000

namespace DimRed

open LatticeProb

/-- Dimensional reduction at one triple, from the earlier instances of the joint
induction. -/
theorem dimred_step_of_earlier (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M)
    (hprior : ∀ d' M' t' : ℕ, regEarlier d M t d' M' t' →
      1 ≤ d' → 2 ≤ M' → Reg d' M' t' ∧ DimRedAt d' M' t')
    (hcritical : ∀ (e q : ℕ) (z : Site e), inSimplex e M z →
        (∀ k : Fin e, 1 < z k) →
        odoUnif (e + 1) (2 * M) q (Fin.snoc z 1) =
          odoUnif (e + 1) (2 * M) q
            (Fin.snoc z 1 + unit (Fin.last e)) + 1 →
        (∀ i : ℕ, 1 ≤ i → i ≤ e → ∀ w : Site i,
            odoUnif (i + 1) (2 * M) q (Fin.snoc w 1) =
              odoUnif i (2 * M) q w) →
        (weak_facet_step (e + 1) M q ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → weak_facet_step i M q) →
        (strong_facet_step (e + 1) M q ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → strong_facet_step i M q) →
        (∀ i : ℕ, 1 ≤ i → i ≤ e + 1 →
          (toppleTime i (M - 1) ≤ ((q - 1 : ℕ) : ℕ∞) →
            simplexMax i M (fun w => odoUnif i (2 * M) (q + 1) w
              - odoUnif i (2 * M) (q - 1) w) ≤ 1)) →
        (∀ (j : ℕ), 1 ≤ j → j ≤ M → (q : ℕ∞) ≤ toppleTime (e + 1) j →
          ∀ w : Site (e + 1), inSimplex (e + 1) M w →
            (∀ i : Fin (e + 1), (M : ℤ) - (j : ℤ) < w i) →
            odoUnif (e + 1) (2 * M) q w =
              odoUnif (e + 1) (2 * j) q (fun i => w i - ((M : ℤ) - (j : ℤ)))) →
        odoUnif (e + 1) (2 * M) (q + 1) (Fin.snoc z 1) =
          odoUnif e (2 * M) (q + 1) z) :
    DimRedAt d M t := by
  intro e he1 hde x hx
  subst hde
  -- the earlier instances at the same dimension and side, earlier time
  have hprev_time : ∀ s : ℕ, s < t → Reg (e + 1) M s ∧ DimRedAt (e + 1) M s := by
    intro s hs
    exact hprior (e + 1) M s (Or.inr (Or.inr ⟨rfl, rfl, hs⟩)) (by omega) hM
  -- the earlier instances at lower dimensions, every time
  have hprev_dim : ∀ i : ℕ, 1 ≤ i → i < e + 1 →
      ∀ s : ℕ, Reg i M s ∧ DimRedAt i M s := by
    intro i hi hid s
    exact hprior i M s (Or.inl hid) hi hM
  cases t with
  | zero =>
    -- at time zero both odometers vanish
    simp only [odoUnif, odo]
  | succ q =>
    have hq : q < q + 1 := Nat.lt_succ_self q
    have hreg_q : Reg (e + 1) M q := (hprev_time q hq).1
    have hweak_q : RegWeak (e + 1) M q := hreg_q.2.1
    have hfacet_q : RegStrongFacet (e + 1) M q := hreg_q.2.2.2.1
    -- the clauses at a lower dimension, at time `q`
    have hreg_low : ∀ i : ℕ, 1 ≤ i → i < e + 1 → Reg i M q := by
      intro i hi hid
      exact (hprev_dim i hi hid q).1
    have hweak : weak_facet_step (e + 1) M q ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ e → weak_facet_step i M q := by
      refine ⟨?_, ?_⟩
      · by_cases hq0 : q = 0
        · subst hq0
          intro z k hz hk h
          simp only [odoUnif, odo] at h
          omega
        · exact weak_facet_step_of_reg (e + 1) M q (by omega) hweak_q
      · intro i hi hie
        by_cases hq0 : q = 0
        · subst hq0
          intro z k hz hk h
          simp only [odoUnif, odo] at h
          omega
        · exact weak_facet_step_of_reg i M q (by omega) (hreg_low i hi (by omega)).2.1
    have hfacet : strong_facet_step (e + 1) M q ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ e → strong_facet_step i M q := by
      refine ⟨?_, ?_⟩
      · by_cases hq0 : q = 0
        · subst hq0
          intro z k hz hk
          simp only [odoUnif, odo]
          norm_num
        · exact strong_facet_step_of_reg (e + 1) M q (by omega) (by omega) hfacet_q
      · intro i hi hie
        by_cases hq0 : q = 0
        · subst hq0
          intro z k hz hk
          simp only [odoUnif, odo]
          norm_num
        · exact strong_facet_step_of_reg i M q (by omega) (by omega)
            (hreg_low i hi (by omega)).2.2.2.1
    have htopple : ∀ i : ℕ, 1 ≤ i → i ≤ e + 1 →
        (toppleTime i (M - 1) ≤ ((q + 1 - 2 : ℕ) : ℕ∞) →
          simplexMax i M (fun w => odoUnif i (2 * M) (q + 1) w
            - odoUnif i (2 * M) (q + 1 - 2) w) ≤ 1) := by
      intro i hi hie hs
      have hq1 : 1 ≤ q := by
        by_contra hc
        have hc0 : q = 0 := by omega
        subst hc0
        have h1 : (1 : ℕ∞) ≤ toppleTime i (M - 1) := one_le_toppleTime i (M - 1)
        have h2 : (1 : ℕ∞) ≤ ((0 + 1 - 2 : ℕ) : ℕ∞) := le_trans h1 hs
        have h3 : (1 : ℕ) ≤ 0 + 1 - 2 := ENat.coe_le_coe.mp h2
        omega
      have hq2 : q + 1 - 2 = q - 1 := by omega
      rw [hq2]
      have hreg_i : Reg i M (q - 1) := by
        by_cases hie' : i ≤ e
        · exact (hprev_dim i hi (by omega) (q - 1)).1
        · have hieq : i = e + 1 := by omega
          subst hieq
          exact (hprev_time (q - 1) (by omega)).1
      have h := hreg_i.2.2.2.2 hs
      have hq3 : q - 1 + 2 = q + 1 := by omega
      rw [hq3] at h
      exact h
    have hconsist : ∀ (j : ℕ), 1 ≤ j → j ≤ M →
        ((q + 1 - 1 : ℕ) : ℕ∞) ≤ toppleTime (e + 1) j →
        ∀ z : Site (e + 1), inSimplex (e + 1) M z →
          (∀ i : Fin (e + 1), (M : ℤ) - (j : ℤ) < z i) →
          odoUnif (e + 1) (2 * M) (q + 1 - 1) z =
            odoUnif (e + 1) (2 * j) (q + 1 - 1)
              (fun i => z i - ((M : ℤ) - (j : ℤ))) := by
      intro j hj1 hj2 hs z hz hzgt
      exact hreg_q.1 j hj1 hj2 hs z hz hzgt
    have hprev : ∀ i : ℕ, 1 ≤ i → i ≤ e → ∀ z : Site i,
          odoUnif (i + 1) (2 * M) (q + 1 - 1) (Fin.snoc z 1) =
            odoUnif i (2 * M) (q + 1 - 1) z := by
      intro i hi hie
      have hred_i : DimRedAt (i + 1) M q := by
        by_cases hlt' : i + 1 < e + 1
        · exact (hprior (i + 1) M q (Or.inl hlt') (by omega) hM).2
        · have hieq : i = e := by omega
          subst hieq
          exact (hprev_time q hq).2
      exact odoUnif_snoc_of_reduction i M q (fun w hw => hred_i i hi rfl w hw)
    have hcritical : 1 ≤ q → ∀ (z : Site e), inSimplex e M z →
        (∀ k : Fin e, 1 < z k) →
        odoUnif (e + 1) (2 * M) (q + 1 - 1) (Fin.snoc z 1) =
          odoUnif (e + 1) (2 * M) (q + 1 - 1)
            (Fin.snoc z 1 + unit (Fin.last e)) + 1 →
        (∀ i : ℕ, 1 ≤ i → i ≤ e → ∀ w : Site i,
            odoUnif (i + 1) (2 * M) (q + 1 - 1) (Fin.snoc w 1) =
              odoUnif i (2 * M) (q + 1 - 1) w) →
        (weak_facet_step (e + 1) M (q + 1 - 1) ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → weak_facet_step i M (q + 1 - 1)) →
        (strong_facet_step (e + 1) M (q + 1 - 1) ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → strong_facet_step i M (q + 1 - 1)) →
        (∀ i : ℕ, 1 ≤ i → i ≤ e + 1 →
          (toppleTime i (M - 1) ≤ ((q + 1 - 2 : ℕ) : ℕ∞) →
            simplexMax i M (fun w => odoUnif i (2 * M) (q + 1) w
              - odoUnif i (2 * M) (q + 1 - 2) w) ≤ 1)) →
        (∀ (j : ℕ), 1 ≤ j → j ≤ M →
          ((q + 1 - 1 : ℕ) : ℕ∞) ≤ toppleTime (e + 1) j →
          ∀ w : Site (e + 1), inSimplex (e + 1) M w →
            (∀ i : Fin (e + 1), (M : ℤ) - (j : ℤ) < w i) →
            odoUnif (e + 1) (2 * M) (q + 1 - 1) w =
              odoUnif (e + 1) (2 * j) (q + 1 - 1)
                (fun i => w i - ((M : ℤ) - (j : ℤ)))) →
        odoUnif (e + 1) (2 * M) (q + 1) (Fin.snoc z 1) =
          odoUnif e (2 * M) (q + 1) z := by
      intro hqpos z hz hz1 hgap hprev' hweak' hfacet' htopple' hconsist'
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with he0 | hpos
        · subst he0
          have h := hz1 ⟨0, by omega⟩
          omega
        · exact hpos
      have hq1 : 2 ≤ q + 1 := by omega
      have hconsist'' : ∀ (j : ℕ), 1 ≤ j → j ≤ M → (q : ℕ∞) ≤ toppleTime e j →
          ∀ w : Site e, inSimplex e M w →
            (∀ i : Fin e, (M : ℤ) - (j : ℤ) < w i) →
            odoUnif e (2 * M) q w =
              odoUnif e (2 * j) q (fun i => w i - ((M : ℤ) - (j : ℤ))) := by
        intro j hj1 hj2 hs w hw hwgt
        exact (hprior e M q (Or.inl (by omega)) (by omega) hM).1.1 j hj1 hj2 hs w hw hwgt
      have hqeq : q + 1 - 1 = q := by omega
      rw [hqeq] at hgap hprev' hweak' hfacet' hconsist'
      have hq2 : q + 1 - 2 = q - 1 := by omega
      rw [hq2] at htopple'
      have hprev : ∀ (s : ℕ) (m : ℕ), s < q + 1 → 2 ≤ m → m ≤ M → ∀ y : Site e,
          inSimplex e m y →
          odoUnif (e + 1) (2 * m) s (Fin.snoc y 1) = odoUnif e (2 * m) s y := by
        intro s m hs hm2 hmM y hy
        have he : regEarlier (e + 1) M (q + 1) (e + 1) m s := by
          by_cases hm : m < M
          · exact Or.inr (Or.inl ⟨rfl, hm⟩)
          · exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)
        exact (hprior (e + 1) m s he (by omega) (by omega)).2 e he1 rfl y hy
      have hprev_one : ∀ (s : ℕ), s < q + 1 → ∀ y : Site e, inSimplex e 1 y →
          odoUnif (e + 1) 2 s (Fin.snoc y 1) = odoUnif e 2 s y := by
        intro s hs y hy
        have hy1 : Fin.snoc y 1 = fun _ : Fin (e + 1) => (1 : ℤ) := by
          funext k
          refine Fin.lastCases ?_ (fun a => ?_) k
          · rw [Fin.snoc_last]
          · rw [Fin.snoc_castSucc]
            have h := (hy.1 a).1
            have h2 := (hy.1 a).2
            omega
        have hy2 : y = fun _ : Fin e => (1 : ℤ) := by
          funext a
          have h := (hy.1 a).1
          have h2 := (hy.1 a).2
          omega
        rw [hy1, hy2, odoUnif_one_scale (e + 1) s (by omega), odoUnif_one_scale e s he1]
      have hgap' : odoUnif (e + 1) (2 * M) ((q + 1) - 1) (Fin.snoc z 1) =
          odoUnif (e + 1) (2 * M) ((q + 1) - 1) (Fin.snoc z 2) + 1 := by
        have hq : q + 1 - 1 = q := by omega
        rw [hq]
        have hsnoc : Fin.snoc z 1 + unit (Fin.last e) = Fin.snoc z 2 := by
          funext k
          refine Fin.lastCases ?_ (fun a => ?_) k
          · rw [Pi.add_apply, Fin.snoc_last, Fin.snoc_last]
            simp [unit]
          · rw [Pi.add_apply, Fin.snoc_castSucc, Fin.snoc_castSucc]
            simp [unit]
        rw [← hsnoc]
        exact hgap
      have hjump : odoUnif (e + 1) (2 * M) ((q + 1) - 1) (Fin.snoc z 1) =
          odoUnif (e + 1) (2 * M) ((q + 1) - 2) (Fin.snoc z 1) + 1 := by
        have hq : q + 1 - 1 = q := by omega
        have hq2 : q + 1 - 2 = q - 1 := by omega
        rw [hq, hq2]
        have hX : inSimplex (e + 1) M (Fin.snoc z 1) := inSimplex_snoc_one_local z hz (by omega)
        have hk : (Fin.snoc z 1 : Site (e + 1)) (Fin.last e) = 1 := by rw [Fin.snoc_last]
        have h2 : ∃ l, 2 ≤ (Fin.snoc z 1 : Site (e + 1)) l :=
          ⟨Fin.castSucc ⟨0, by omega⟩, by
            rw [Fin.snoc_castSucc]
            exact hz1 ⟨0, by omega⟩⟩
        have hS : RegStrongFacet (e + 1) M ((q + 1) - 2) :=
          (hprior (e + 1) M ((q + 1) - 2) (Or.inr (Or.inr ⟨rfl, rfl, by omega⟩))
            (by omega) (by omega)).1.2.2.2.1
        have h := odo_jump_of_gap (d := e + 1) (M := M) (t := q + 1) (by omega) hM (by omega) hS
          (Fin.snoc z 1) hX (Fin.last e) hk h2 hgap
        have h1 : q + 1 - 1 = q := by omega
        have h2' : q + 1 - 2 = q - 1 := by omega
        rw [h1, h2'] at h
        exact h
      have htopple_up : toppleTime (e + 1) (M - 1) ≤ (((q + 1) - 2 : ℕ) : ℕ∞) →
          simplexMax (e + 1) M (fun w => odoUnif (e + 1) (2 * M) (q + 1) w
            - odoUnif (e + 1) (2 * M) ((q + 1) - 2) w) ≤ 1 := by
        intro hs
        have hq2 : q + 1 - 2 = q - 1 := by omega
        rw [hq2] at hs ⊢
        exact htopple' (e + 1) (by omega) (by omega) hs
      have htopple_down : toppleTime (e + 1) (M - 1) ≤ (((q + 1) - 2 : ℕ) : ℕ∞) →
          simplexMax e M (fun w => odoUnif e (2 * M) (q + 1) w
            - odoUnif e (2 * M) ((q + 1) - 2) w) ≤ 1 := by
        intro hs
        have hq2 : q + 1 - 2 = q - 1 := by omega
        rw [hq2] at hs ⊢
        -- the topple time in dimension e is at most the one in dimension e+1, from
        -- dimensional reduction at the corner at every earlier time
        have hmono : toppleTime e (M - 1) ≤ toppleTime (e + 1) (M - 1) := by
          by_cases hM3 : 3 ≤ M
          · have hM3' : 2 ≤ M - 1 := by omega
            have hred : ∀ (t : ℕ) (y : Site e), inSimplex e (M - 1) y →
                odoUnif (e + 1) (2 * (M - 1)) t (Fin.snoc y 1) =
                  odoUnif e (2 * (M - 1)) t y := by
              intro t y hy
              exact (hprior (e + 1) (M - 1) t
                (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega) hM3').2 e (by omega) rfl y hy
            have hred' : ∀ (e' : ℕ), 1 ≤ e' → e' < e + 1 → ∀ (t : ℕ) (y : Site e'),
                inSimplex e' (M - 1) y →
                odoUnif (e' + 1) (2 * (M - 1)) t (Fin.snoc y 1) =
                  odoUnif e' (2 * (M - 1)) t y := by
              intro e' he' he'l t y hy
              rcases lt_or_eq_of_le (by omega : e' ≤ e) with hlt | heq
              · exact (hprior (e' + 1) (M - 1) t (Or.inl (by omega)) (by omega)
                  hM3').2 e' he' rfl y hy
              · cases heq
                exact (hprior (e + 1) (M - 1) t
                  (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega) hM3').2 e he' rfl y hy
            exact toppleTime_mono_dim e (M - 1) (by omega) (by omega) hred hred'
          · -- M = 2: the topple time is one in every dimension
            have hM2 : M = 2 := by omega
            subst hM2
            have h1 : toppleTime e 1 = 1 := by
              have hle : toppleTime e 1 ≤ 1 := by
                rw [toppleTime_eq_corner e 1 (by omega) (by omega)]
                apply sInf_le
                exact ⟨1, ⟨by norm_num, corner_one_le e⟩, rfl⟩
              exact le_antisymm hle (one_le_toppleTime e 1)
            have h2 : toppleTime (e + 1) 1 = 1 := by
              have hle : toppleTime (e + 1) 1 ≤ 1 := by
                rw [toppleTime_eq_corner (e + 1) 1 (by omega) (by omega)]
                apply sInf_le
                exact ⟨1, ⟨by norm_num, corner_one_le (e + 1)⟩, rfl⟩
              exact le_antisymm hle (one_le_toppleTime (e + 1) 1)
            rw [h1, h2]
        exact htopple' e (by omega) (by omega) (le_trans hmono hs)
      have hconsist : (((q + 1) - 1 : ℕ) : ℕ∞) ≤ toppleTime (e + 1) (M - 1) →
          odoUnif (e + 1) (2 * M) ((q + 1) - 1) (Fin.snoc z 2)
            = odoUnif (e + 1) (2 * (M - 1)) ((q + 1) - 1) (Fin.snoc (fun k => z k - 1) 1) ∧
          odoUnif e (2 * M) ((q + 1) - 1) z = odoUnif e (2 * (M - 1)) ((q + 1) - 1) (fun k => z k - 1) := by
        intro hs
        have hq : q + 1 - 1 = q := by omega
        rw [hq] at hs ⊢
        have hMsub : (M : ℤ) - ((M - 1 : ℕ) : ℤ) = 1 := by omega
        have hsnoc : (fun i : Fin (e + 1) => (Fin.snoc z 2 : Site (e + 1)) i - 1)
            = Fin.snoc (fun k => z k - 1) 1 := by
          funext k
          refine Fin.lastCases ?_ (fun a => ?_) k
          · rw [Fin.snoc_last, Fin.snoc_last]
            norm_num
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        constructor
        · rw [← hsnoc]
          have hgoal : (fun i : Fin (e + 1) => (Fin.snoc z 2 : Site (e + 1)) i - 1)
              = (fun i => (Fin.snoc z 2 : Site (e + 1)) i - ((M : ℤ) - ((M - 1 : ℕ) : ℤ))) := by
            funext i
            rw [hMsub]
          rw [hgoal]
          exact (hconsist' (M - 1) (by omega) (by omega) hs (Fin.snoc z 2)
            (inSimplex_snoc_two_local z hz hz1 hM)
            (fun i => by
              refine Fin.lastCases ?_ (fun a => ?_) i
              · rw [Fin.snoc_last]
                omega
              · rw [Fin.snoc_castSucc]
                have h1 := (hz.1 a).1
                have h3 := hz1 a
                omega))
        · have hmono : toppleTime (e + 1) (M - 1) ≤ toppleTime e (M - 1) := by
            by_cases hM3 : 3 ≤ M
            · have hM3' : 2 ≤ M - 1 := by omega
              have hred : ∀ (t : ℕ) (y : Site e), inSimplex e (M - 1) y →
                  odoUnif (e + 1) (2 * (M - 1)) t (Fin.snoc y 1) =
                    odoUnif e (2 * (M - 1)) t y := by
                intro t y hy
                exact (hprior (e + 1) (M - 1) t
                  (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega) hM3').2 e (by omega) rfl y hy
              have hred' : ∀ (e' : ℕ), 1 ≤ e' → e' < e + 1 → ∀ (t : ℕ) (y : Site e'),
                  inSimplex e' (M - 1) y →
                  odoUnif (e' + 1) (2 * (M - 1)) t (Fin.snoc y 1) =
                    odoUnif e' (2 * (M - 1)) t y := by
                intro e' he' he'l t y hy
                rcases lt_or_eq_of_le (by omega : e' ≤ e) with hlt | heq
                · exact (hprior (e' + 1) (M - 1) t (Or.inl (by omega)) (by omega)
                    hM3').2 e' he' rfl y hy
                · cases heq
                  exact (hprior (e + 1) (M - 1) t
                    (Or.inr (Or.inl ⟨rfl, by omega⟩)) (by omega) hM3').2 e he' rfl y hy
              exact toppleTime_mono_dim_le e (M - 1) (by omega) (by omega) hred hred'
            · have hM2 : M = 2 := by omega
              subst hM2
              have h1 : toppleTime e 1 = 1 := by
                have hle : toppleTime e 1 ≤ 1 := by
                  rw [toppleTime_eq_corner e 1 (by omega) (by omega)]
                  apply sInf_le
                  exact ⟨1, ⟨by norm_num, corner_one_le e⟩, rfl⟩
                exact le_antisymm hle (one_le_toppleTime e 1)
              have h2 : toppleTime (e + 1) 1 = 1 := by
                have hle : toppleTime (e + 1) 1 ≤ 1 := by
                  rw [toppleTime_eq_corner (e + 1) 1 (by omega) (by omega)]
                  apply sInf_le
                  exact ⟨1, ⟨by norm_num, corner_one_le (e + 1)⟩, rfl⟩
                exact le_antisymm hle (one_le_toppleTime (e + 1) 1)
              rw [h1, h2]
          have h := hconsist'' (M - 1) (by omega) (by omega) (le_trans hs hmono) z hz
            (fun i => by
              have h1 := (hz.1 i).1
              have h3 := hz1 i
              omega)
          simpa only [hMsub] using h
      exact odo_dimred_critical e M (q + 1) he1 hM hq1 z hz hz1 hprev hprev_one hgap' hjump
        htopple_up htopple_down hconsist

    have hcrit : ∀ (z : Site e), inSimplex e M z →
        (∀ k : Fin e, 1 < z k) →
        odoUnif (e + 1) (2 * M) (q + 1 - 1) (Fin.snoc z 1) =
          odoUnif (e + 1) (2 * M) (q + 1 - 1)
            (Fin.snoc z 1 + unit (Fin.last e)) + 1 →
        (∀ i : ℕ, 1 ≤ i → i ≤ e → ∀ w : Site i,
            odoUnif (i + 1) (2 * M) (q + 1 - 1) (Fin.snoc w 1) =
              odoUnif i (2 * M) (q + 1 - 1) w) →
        (weak_facet_step (e + 1) M (q + 1 - 1) ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → weak_facet_step i M (q + 1 - 1)) →
        (strong_facet_step (e + 1) M (q + 1 - 1) ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ e → strong_facet_step i M (q + 1 - 1)) →
        (∀ i : ℕ, 1 ≤ i → i ≤ e + 1 →
          (toppleTime i (M - 1) ≤ ((q + 1 - 2 : ℕ) : ℕ∞) →
            simplexMax i M (fun w => odoUnif i (2 * M) (q + 1) w
              - odoUnif i (2 * M) (q + 1 - 2) w) ≤ 1)) →
        (∀ (j : ℕ), 1 ≤ j → j ≤ M →
          ((q + 1 - 1 : ℕ) : ℕ∞) ≤ toppleTime (e + 1) j →
          ∀ w : Site (e + 1), inSimplex (e + 1) M w →
            (∀ i : Fin (e + 1), (M : ℤ) - (j : ℤ) < w i) →
            odoUnif (e + 1) (2 * M) (q + 1 - 1) w =
              odoUnif (e + 1) (2 * j) (q + 1 - 1)
                (fun i => w i - ((M : ℤ) - (j : ℤ)))) →
        odoUnif (e + 1) (2 * M) (q + 1) (Fin.snoc z 1) =
          odoUnif e (2 * M) (q + 1) z := by
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        intro z hz hz1 hgap hprev' hweak' hfacet' htopple' hconsist'
        have h1 : odoUnif (e + 1) (2 * M) 1 (Fin.snoc z 1) = 1 :=
          odoUnif_one (e + 1) (2 * M) (by omega) _
            (inSimplex_inCube (e + 1) M (Fin.snoc z 1)
              (inSimplex_snoc_one_local z hz (by omega)))
        have h2 : odoUnif e (2 * M) 1 z = 1 :=
          odoUnif_one e (2 * M) (by omega) _ (inSimplex_inCube e M z hz)
        rw [h1, h2]
      · exact hcritical hqpos
    exact odo_dimred_step e M (q + 1) (by omega) hM x hx hprev hweak hfacet htopple
      hconsist hcrit

end DimRed
