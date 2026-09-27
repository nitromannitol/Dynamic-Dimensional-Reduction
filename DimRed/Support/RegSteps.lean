/-
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
import DimRed.Support.RegBridges
import DimRed.Support.SimplexFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
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
  have hprev_dim : ∀ i : ℕ, 1 ≤ i → i < e + 1 → ∀ s : ℕ, Reg i M s ∧ DimRedAt i M s := by
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
    have hcritical : ∀ (z : Site e), inSimplex e M z →
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
      intro z hz hz1 hgap hprev' hweak' hfacet' htopple' hconsist'
      exact hcritical e q z hz hz1 (by simpa using hgap) hprev' hweak' hfacet'
        (fun i hi hie hs => by
          have h := htopple' i hi hie hs
          have hq2 : q + 1 - 2 = q - 1 := by omega
          rw [hq2] at h
          exact h)
        (fun j hj1 hj2 hs w hw hwgt => hconsist' j hj1 hj2 (by simpa using hs) w hw hwgt)
    exact odo_dimred_step e M (q + 1) (by omega) hM x hx hprev hweak hfacet htopple hconsist hcritical

end DimRed
